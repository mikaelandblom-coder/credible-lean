// Does the skew of the region *levels* (not the noise) bias the plug-in fits? Portfolio bias of the
// unbalanced fits against BS on the same draws (BS is balanced: portfolio bias 0 exactly), with the
// app's gamma levels (shape 4, skewness 1) and nearly symmetric ones (shape 400). % of the tariff, ± 2 SE.
// Run: node studies/runs/level-skew-bias.js [draws]
'use strict';
const E = require('../../app/engine.js');
const N = +(process.argv[2] || 2000);
const sum = (a) => a.reduce((s, x) => s + x, 0);
const ids = ['vc', 'blup', 'blupPool'];
console.log(`draws ${N}; portfolio bias in % (unbalanced), levels skewed (shape 4) | symmetric (shape 400)`);
for (const p of [{}, { rho: 0.6 }, { J: 20 }, { J: 20, rho: 0.3 }, { J: 20, rho: 0.6 }, { J: 20, rho: 0.6, normal: true }, { J: 20, rho: 0.6, tau: 0.2 }]) {
  const cells = ids.map((id) => [4, 400].map((ls) => {
    const w = E.makeWorld(Object.assign({ levelShape: ls }, p)), wt = w.w.map(sum), wall = sum(wt), r = E.rng(91), v = [];
    for (let n = 0; n < N; n++) { const d = E.draw(w, r).data, f = E.MODELS[id].fit(d), g = E.fitBS(d); v.push(sum(f.rates.map((x, j) => wt[j] * (x - g.rates[j]))) / wall); }
    const m = sum(v) / N, se = Math.sqrt(sum(v.map((x) => (x - m) ** 2)) / N / N);
    return `${(100 * m).toFixed(2).padStart(6)} ± ${(200 * se).toFixed(2)}`;
  }).join(' | '));
  console.log(JSON.stringify(p).padEnd(36) + ids.map((id, i) => `${id}: ${cells[i]}`).join('   '));
}
