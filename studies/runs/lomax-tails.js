// How the fits behave as the claim tail gets heavier (PLAN, cumulant layer: "Lomax claims" world).
// Same two moments in every world, so the floor (true K) is the same; only the noise shape changes.
// Per world: MSE of each fit in % above the floor (unbalanced and balanced), the portfolio bias
// (exposure-weighted mean error, unbalanced), and corrBS's jackknife MSEP against its actual MSE.
// Run: node studies/runs/lomax-tails.js [draws] [seed]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 3000), SEED = +(process.argv[3] || 1);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const ids = ['bs', 'vc', 'blup', 'blupPool'];
const worlds = [['gamma (default)', {}], ['normal', { normal: true }]]
  .concat([8, 5, 4, 3.5, 3, 2.5, 2.2].map((a) => [`Lomax α = ${a}`, { lomax: a }]));
const extra = (process.argv[4] && JSON.parse(process.argv[4])) || {};

const pct = (x) => (x >= 0 ? '+' : '') + (100 * x).toFixed(1);
console.log(`draws ${N}, seed ${SEED}, world ${JSON.stringify(extra)}`);
console.log('world'.padEnd(17) + ids.map((i) => (i + ' raw/bal').padStart(16)).join('') + '   bias vc (bp ± se)   jk MSEP/MSE vc (median per draw)');
for (const [name, p] of worlds) {
  const world = E.makeWorld(Object.assign({}, extra, p));
  const raw = E.simulate(world, ids, N, SEED, 1, { balance: false });
  const bal = E.simulate(world, ids, N, SEED, 1, { balance: true });
  const fl = raw.floor.mse;
  const cols = ids.map((i) => `${pct(raw[i].mse / fl - 1)}/${pct(bal[i].mse / fl - 1)}`.padStart(16)).join('');
  const b = raw.vc.bias;
  // Jackknife MSEP of corrBS: exposure-weighted predicted MSEP against the squared error, per draw.
  const r = E.rng(SEED * 31 + 7), wt = world.w.map(sum), wall = sum(wt);
  let pred = 0, act = 0; const ratios = [];
  const M = Math.min(N, 1000);
  for (let k = 0; k < M; k++) {
    const { levels, data } = E.draw(world, r), jk = E.jackknifeMSEP(data);
    const pk = sum(jk.msep.map((x, j) => wt[j] * x)) / wall, ak = sum(jk.rates.map((x, j) => wt[j] * (x - levels[j]) ** 2)) / wall;
    pred += pk; act += ak; ratios.push(pk);
  }
  ratios.sort((x, y) => x - y);
  const med = ratios[M >> 1] / (act / M);
  console.log(name.padEnd(17) + cols + `   ${(1e4 * b.mean).toFixed(0).padStart(4)} ± ${(1e4 * b.se).toFixed(0).padEnd(4)}       ${(pred / act).toFixed(2)} (${med.toFixed(2)})`);
}
