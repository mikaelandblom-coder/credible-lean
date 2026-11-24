// Shared helpers for the simulation studies (conventions in studies/PLAN.md, "Study conventions").
//   grid(axes)          — every combination of the axes' values (a full factorial design);
//   paired(a, b)        — mean of a − b over the same draws with its Monte Carlo SE (common random numbers);
//   meanSE(x)           — mean and SE of one column;
//   pm(m, se, scale)    — "m ± 2SE" scaled (e.g. to % of a floor), for the tables;
//   regimes             — the credibility regimes every engine study should report (z of the floor):
//                         'app' (volume 500: z ≈ 0.2–0.9, the app default) and 'thesis' (volume 4400:
//                         z ≈ 0.7–1.0, the regime of the thesis's expert-judgement study, §4 Table 4.1).
'use strict';
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
const regimes = { app: { volume: 500 }, thesis: { volume: 4400 } };

module.exports = { sum, grid, meanSE, paired, pm, regimes };
