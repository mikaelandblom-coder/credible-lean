// Shared helpers for the simulation studies (conventions in studies/PLAN.md, "Study conventions").
//   grid(axes)          — every combination of the axes' values (a full factorial design);
//   paired(a, b)        — mean of a − b over the same draws with its Monte Carlo SE (common random numbers);
//   meanSE(x)           — mean and SE of one column;
//   pm(m, se, scale)    — "m ± 2SE" scaled (e.g. to % of a floor), for the tables;
//   regimes             — the credibility regimes every engine study should report (z of the floor):
//                         'app' (volume 500: z ≈ 0.2–0.9, the app default) and 'thesis' (volume 4400:
//                         z ≈ 0.7–1.0, the regime of the thesis's expert-judgement study, §4 Table 4.1);
//                         'thesisShape' adds that table's shape: volumes nearly equal (wⱼ sd 1%) and σⱼ²
//                         spread like lognormal(16, √2) (noiseSpread 2: σⱼ² × 1/16–16).
//   args()              — the command line: draws N (first number, default 400), --jobs=k (default: all cores),
//                         --only=a,b (fit ids to run; empty = all);
//   mapWorlds(file, worlds, fn, jobs, cost) — fn(world, index) for every world, on a pool of `jobs` worker threads
//                         (heaviest first by the optional cost(world))
//                         (each runs `file`, the study itself); resolves to the results in order. fn must be
//                         deterministic per world (its own seed) and return plain data. In a worker the
//                         promise never resolves, so the study's printing runs only in the main thread.
//   sig(d, tol)         — +1 / −1 / 0: a paired difference beyond 2 SE (and beyond tol, which keeps float
//                         noise between identical fits, ~1e−16, from counting as a win or a loss).
'use strict';
const os = require('node:os');
const { Worker, isMainThread, parentPort, workerData } = require('node:worker_threads');
const sum = (a) => a.reduce((s, x) => s + x, 0);

function grid(axes) {
  return Object.entries(axes).reduce((acc, [k, vals]) => acc.flatMap((o) => vals.map((v) => Object.assign({}, o, { [k]: v }))), [{}]);
}
function meanSE(x) {
  const n = x.length, m = sum(x) / n, v = sum(x.map((y) => (y - m) ** 2)) / (n - 1);
  return { m, se: Math.sqrt(v / n), n };
}
const paired = (a, b) => meanSE(a.map((x, i) => x - b[i]));
const pm = (r, scale) => `${(r.m * (scale || 1)).toFixed(1)} ± ${(2 * r.se * (scale || 1)).toFixed(1)}`;
const regimes = { app: { volume: 500 }, thesis: { volume: 4400 }, thesisShape: { volume: 4400, spread: 0.05, noiseSpread: 2 } };

function args(argv) {
  const a = argv || process.argv.slice(2), num = a.find((x) => /^\d+$/.test(x));
  const opt = (k) => { const x = a.find((y) => y.startsWith(`--${k}=`)); return x ? x.slice(k.length + 3) : null; };
  const only = opt('only');
  return { N: num ? +num : 400, jobs: Math.max(1, +(opt('jobs') || os.cpus().length)), only: only ? only.split(',') : null };
}

function mapWorlds(file, worlds, fn, jobs, cost) {
  if (!isMainThread) {
    // a pool worker: compute the worlds the main thread sends, one at a time, until it sends null
    if (workerData && workerData.__mapWorlds) parentPort.on('message', (i) => { if (i === null) parentPort.close(); else parentPort.postMessage({ i, r: fn(worlds[i], i) }); });
    return new Promise(() => {});
  }
  const n = Math.min(jobs || 1, worlds.length);
  if (n <= 1) return Promise.resolve(worlds.map(fn));
  // a pool of n persistent workers, each handed the next world when it reports one (balances unequal worlds)
  // heaviest first (cost(world), if given): a slow world started last would leave the other cores idle
  const order = worlds.map((_, i) => i);
  if (cost) order.sort((a, b) => cost(worlds[b]) - cost(worlds[a]));
  const out = new Array(worlds.length);
  let nextI = 0, left = worlds.length;
  return new Promise((resolve, reject) => {
    for (let k = 0; k < n; k++) {
      const w = new Worker(file, { workerData: { __mapWorlds: true }, argv: process.argv.slice(2) });
      const feed = () => w.postMessage(nextI < worlds.length ? order[nextI++] : null);
      w.on('message', ({ i, r }) => { out[i] = r; if (--left === 0) resolve(out); feed(); });
      w.on('error', reject);
      feed();
    }
  });
}

const sig = (d, tol) => (Math.abs(d.m) <= (tol || 0) ? 0 : d.m - 2 * d.se > 0 ? 1 : d.m + 2 * d.se < 0 ? -1 : 0);

module.exports = { sum, grid, meanSE, paired, pm, regimes, args, mapWorlds, sig, isMainThread };
