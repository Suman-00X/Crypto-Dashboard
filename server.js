const express = require('express');
const cors = require('cors');
const axios = require('axios');
const crypto = require('crypto');
require('dotenv').config();

const app = express();
const PORT = process.env.PORT || 5000;
const MAX_CANDLE_DAYS = 400;
const PAGE_SIZES = new Set([20, 50, 100, 200]);
const INDEX_TTL_MS = 3 * 60 * 1000;
const PATH_TTL_MS = 3 * 60 * 1000;
const MAX_BARS = 5000;
const CANDLE_PAGE = 1000;

const INTERVAL_MS = {
  '1m': 60_000,
  '5m': 5 * 60_000,
  '15m': 15 * 60_000,
  '30m': 30 * 60_000,
  '1h': 60 * 60_000,
  '4h': 4 * 60 * 60_000,
  '1d': 24 * 60 * 60_000,
};

const DEFAULT_ORIGINS = [
  'http://localhost:5173',
  'http://localhost:5174',
  'https://crypto-dashboard-3mk1.onrender.com',
  'https://crypto-suman.netlify.app',
];

const envOrigins = String(process.env.CORS_ORIGINS || '')
  .split(',')
  .map((s) => s.trim().replace(/\/$/, ''))
  .filter(Boolean);

const allowedOrigins = [...new Set([...DEFAULT_ORIGINS, ...envOrigins])];

app.use(
  cors({
    origin(origin, callback) {
      // Non-browser / same-origin requests may omit Origin
      if (!origin) return callback(null, true);

      const normalized = origin.replace(/\/$/, '');
      if (allowedOrigins.includes(normalized)) {
        return callback(null, true);
      }

      // Allow project frontends hosted on Render or Netlify
      if (/^https:\/\/[\w-]+\.onrender\.com$/i.test(normalized)) {
        return callback(null, true);
      }
      if (/^https:\/\/[\w-]+\.netlify\.app$/i.test(normalized)) {
        return callback(null, true);
      }

      // Optional escape hatch for temporary debugging
      if (process.env.CORS_ALLOW_ALL === 'true') {
        return callback(null, true);
      }

      return callback(new Error(`CORS blocked for origin: ${origin}`));
    },
    credentials: true,
  })
);
app.use(express.json());

const USER_DB = {
  admin: { password: 'Admin@123' },
};

const activeSessions = new Map();
let indexCache = { timestamp: 0, markets: null };
const pathCache = new Map();

function requireAuth(req, res, next) {
  const token = req.headers.authorization;
  if (!token || !activeSessions.has(token)) {
    return res.status(401).json({ error: 'Unauthorized. Session expired or invalid.' });
  }
  next();
}

app.post('/api/auth/login', (req, res) => {
  const { username, password } = req.body;
  const user = USER_DB[username];
  if (!user || password !== user.password) {
    return res.status(401).json({ error: 'Invalid username or password' });
  }
  const sessionToken = crypto.randomBytes(32).toString('hex');
  activeSessions.set(sessionToken, { username, createdAt: Date.now() });
  res.json({ token: sessionToken, username });
});

app.post('/api/auth/logout', (req, res) => {
  const token = req.headers.authorization;
  if (token) activeSessions.delete(token);
  res.json({ success: true });
});

async function getMarketIndex() {
  const now = Date.now();
  if (indexCache.markets && now - indexCache.timestamp < INDEX_TTL_MS) {
    return indexCache.markets;
  }

  const [tickerRes, detailsRes] = await Promise.all([
    axios.get('https://api.coindcx.com/exchange/ticker', { timeout: 20000 }),
    axios.get('https://api.coindcx.com/exchange/v1/markets_details', { timeout: 20000 }),
  ]);

  const tickerByMarket = new Map(tickerRes.data.map((t) => [t.market, t]));

  const markets = detailsRes.data
    .filter(
      (m) =>
        m.base_currency_short_name === 'USDT' &&
        m.status === 'active' &&
        m.pair &&
        m.coindcx_name
    )
    .map((m) => {
      const ticker = tickerByMarket.get(m.coindcx_name) || tickerByMarket.get(m.symbol);
      if (!ticker) return null;
      return {
        pair: m.pair,
        market: m.coindcx_name,
        symbol: m.target_currency_short_name,
        change24h: parseFloat(ticker.change_24_hour) || 0,
        volume24h: parseFloat(ticker.volume) || 0,
        high24h: parseFloat(ticker.high) || 0,
        low24h: parseFloat(ticker.low) || 0,
        lastPrice: parseFloat(ticker.last_price) || 0,
      };
    })
    .filter(Boolean)
    .sort((a, b) => b.volume24h - a.volume24h);

  indexCache = { timestamp: now, markets };
  return markets;
}

/** Finest candle interval that still fits ~MAX_BARS for N days. */
function pickInterval(days) {
  const candidates = [
    ['1m', 1440],
    ['5m', 288],
    ['15m', 96],
    ['30m', 48],
    ['1h', 24],
    ['4h', 6],
    ['1d', 1],
  ];
  for (const [iv, perDay] of candidates) {
    if (days * perDay <= MAX_BARS) return iv;
  }
  return '1d';
}

/**
 * Expand a candle into an open→extrema→close polyline with millisecond stamps.
 * True trade ticks (also ms) are merged on top later.
 */
function candleToMsPoints(candle, barMs) {
  const t0 = Number(candle.time);
  const o = parseFloat(candle.open);
  const h = parseFloat(candle.high);
  const l = parseFloat(candle.low);
  const c = parseFloat(candle.close);
  const v = parseFloat(candle.volume) || 0;
  if (!(o > 0) || !(c > 0) || !(h > 0) || !(l > 0)) return [];

  // Bullish: O → L → H → C ; Bearish: O → H → L → C
  const midA = c >= o ? l : h;
  const midB = c >= o ? h : l;
  const share = v / 4;

  return [
    { t: t0, p: o, v: share, src: 'candle' },
    { t: t0 + Math.floor(barMs * 0.25), p: midA, v: share, src: 'candle' },
    { t: t0 + Math.floor(barMs * 0.75), p: midB, v: share, src: 'candle' },
    { t: t0 + barMs, p: c, v: share, src: 'candle' },
  ];
}

async function fetchCandlesPaged(pair, interval, windowMs) {
  const barMs = INTERVAL_MS[interval];
  const needed = Math.min(MAX_BARS, Math.ceil(windowMs / barMs) + 2);
  const candles = [];
  let endTime = Date.now();
  let pages = 0;
  const maxPages = Math.ceil(needed / CANDLE_PAGE) + 1;

  while (candles.length < needed && pages < maxPages) {
    pages += 1;
    const { data } = await axios.get(
      'https://public.coindcx.com/market_data/candles/',
      {
        params: {
          pair,
          interval,
          limit: CANDLE_PAGE,
          endTime,
        },
        timeout: 20000,
      }
    );
    if (!Array.isArray(data) || data.length === 0) break;

    candles.push(...data);
    const oldest = Number(data[data.length - 1].time);
    if (Date.now() - oldest >= windowMs) break;
    endTime = oldest - 1;
    if (data.length < CANDLE_PAGE) break;
  }

  // newest-first unique by time
  const byTime = new Map();
  for (const c of candles) byTime.set(Number(c.time), c);
  return [...byTime.values()].sort((a, b) => Number(b.time) - Number(a.time));
}

async function fetchRecentTrades(pair) {
  try {
    const { data } = await axios.get(
      'https://public.coindcx.com/market_data/trade_history',
      { params: { pair, limit: 500 }, timeout: 15000 }
    );
    if (!Array.isArray(data)) return [];
    return data
      .map((tr) => ({
        t: Number(tr.T),
        p: parseFloat(tr.p),
        v: parseFloat(tr.q) || 0,
        src: 'trade',
      }))
      .filter((x) => x.t > 0 && x.p > 0)
      .sort((a, b) => a.t - b.t);
  } catch {
    return [];
  }
}

function mergePaths(candlePoints, trades) {
  if (!trades.length) return candlePoints;
  const tradeStart = trades[0].t;
  // Keep candle path for history; replace latest tip with real ms trades
  const older = candlePoints.filter((pt) => pt.t < tradeStart);
  const merged = [...older, ...trades];
  merged.sort((a, b) => a.t - b.t);
  // de-dupe identical timestamps preferring trades
  const out = [];
  for (const pt of merged) {
    const last = out[out.length - 1];
    if (last && last.t === pt.t) {
      if (pt.src === 'trade') out[out.length - 1] = pt;
      continue;
    }
    out.push(pt);
  }
  return out;
}

function minPositiveDeltaMs(points) {
  let min = Infinity;
  for (let i = 1; i < points.length; i++) {
    const d = points[i].t - points[i - 1].t;
    if (d > 0 && d < min) min = d;
  }
  return Number.isFinite(min) ? min : null;
}

async function buildMsPath(pair, candleDays) {
  const now = Date.now();
  const cached = pathCache.get(pair);
  // Reuse a longer (or equal) cached path for this pair — no rebuild on paging / shallower asks
  if (
    cached &&
    now - cached.timestamp < PATH_TTL_MS &&
    cached.candleDays >= candleDays &&
    cached.payload?.pricePath?.length
  ) {
    return {
      ...cached.payload,
      reusedFromDays: cached.candleDays,
      cacheHit: true,
    };
  }

  const windowMs = candleDays * 24 * 60 * 60 * 1000;
  const interval = pickInterval(candleDays);
  const barMs = INTERVAL_MS[interval];

  const [candles, trades] = await Promise.all([
    fetchCandlesPaged(pair, interval, windowMs),
    fetchRecentTrades(pair),
  ]);

  if (!candles.length && !trades.length) return null;

  const chronological = [...candles].reverse();
  const candlePoints = chronological.flatMap((c) => candleToMsPoints(c, barMs));
  const path = mergePaths(candlePoints, trades);

  const chartCandles =
    candles.length > 0
      ? candles
      : trades.map((tr) => ({
          time: tr.t,
          open: tr.p,
          high: tr.p,
          low: tr.p,
          close: tr.p,
          volume: tr.v,
        }));

  const payload = {
    rawCandles: chartCandles,
    pricePath: path,
    resolution: interval,
    minDeltaMs: minPositiveDeltaMs(path),
    pathPoints: path.length,
    tradeTicks: trades.length,
    cacheHit: false,
  };

  pathCache.set(pair, { timestamp: now, candleDays, payload });
  return payload;
}

async function hydrateMarket(marketMeta, candleDays) {
  try {
    const built = await buildMsPath(marketMeta.pair, candleDays);
    if (!built || !built.pricePath?.length) return null;
    const last = built.pricePath[built.pricePath.length - 1];
    return {
      ...marketMeta,
      currentPrice: last?.p ?? marketMeta.lastPrice,
      ...built,
    };
  } catch (err) {
    console.error('hydrate', marketMeta.pair, err.message);
    return null;
  }
}

app.get('/api/market-trends', requireAuth, async (req, res) => {
  try {
    const page = Math.max(1, parseInt(req.query.page, 10) || 1);
    const requestedLimit = parseInt(req.query.limit, 10) || 50;
    const limit = PAGE_SIZES.has(requestedLimit) ? requestedLimit : 50;
    const candleDays = Math.min(
      MAX_CANDLE_DAYS,
      Math.max(1, parseInt(req.query.candleDays, 10) || 45)
    );
    const search = String(req.query.search || '')
      .trim()
      .toLowerCase();

    const allMarkets = await getMarketIndex();
    const filtered = search
      ? allMarkets.filter((m) => {
          const hay = `${m.symbol} ${m.pair} ${m.market}`.toLowerCase();
          return hay.includes(search);
        })
      : allMarkets;

    const total = filtered.length;
    const totalPages = Math.max(1, Math.ceil(total / limit));
    const safePage = Math.min(page, totalPages);
    const start = (safePage - 1) * limit;
    const pageMarkets = filtered.slice(start, start + limit);

    // gentle concurrency — path builds hit candles + trades
    const data = [];
    const batchSize = 8;
    for (let i = 0; i < pageMarkets.length; i += batchSize) {
      const chunk = pageMarkets.slice(i, i + batchSize);
      const part = await Promise.all(chunk.map((m) => hydrateMarket(m, candleDays)));
      data.push(...part.filter(Boolean));
    }

    const sample = data[0];
    const cacheHits = data.filter((d) => d.cacheHit).length;
    res.json({
      source: 'api',
      data,
      page: safePage,
      limit,
      total,
      totalPages,
      candleDays,
      count: data.length,
      resolution: sample?.resolution || pickInterval(candleDays),
      minDeltaMs: sample?.minDeltaMs ?? null,
      cacheHits,
    });
  } catch (err) {
    console.error('market-trends error:', err.message);
    res.status(500).json({ error: 'Failed to crawl and cache market profiles' });
  }
});

app.listen(PORT, () => console.log(`Secure Aggregator Service active on port ${PORT}`));
