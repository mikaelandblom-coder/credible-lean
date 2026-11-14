// Oracle θ* for the stand-in loss E Σ (θŝᵢⱼ − sᵢⱼ)², from the true variance of Σ̂ᵢⱼ over 20000 draws.
const E = require('../app/engine.js');
const LAWS = { normal: (r) => r.normal(), 'gamma¼': (r) => { const g = r.gamma(1.25) * Math.pow(r(), 4); return (g - 0.25) / 0.5; } };
for (const [name, law] of Object.entries(LAWS)) for (const rho of [0.3, 0.9]) {
  const world = E.makeWorld({ J: 8, T: 10, rho }), K = E.trueK(world), r = E.rng(9), J = 8, N = 20000;
  r.skewed = (k) => (k === world.params.noiseShape ? law(r) : (r.gamma(k) - k) / Math.sqrt(k));
  const s1 = [], s2 = []; for (let i = 0; i < J * J; i++) { s1.push(0); s2.push(0); }
  for (let n = 0; n < N; n++) { const { Sig } = E.sigmaHat(E.draw(world, r).data);
    for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { s1[i * J + j] += Sig[i][j]; s2[i * J + j] += Sig[i][j] ** 2; } }
  let S = 0, V = 0, Sc = 0, Vc = 0;
  for (let i = 0; i < J; i++) for (let j = i + 1; j < J; j++) { const m = s1[i * J + j] / N, v = s2[i * J + j] / N - m * m, s = K[i][j], sc = (K[i][i] - world.truth.tau2) * (K[j][j] - world.truth.tau2);
    S += s * s; V += v; Sc += s * s / sc; Vc += v / sc; }
  console.log(name, 'ρ', rho, ' oracle proxy θ* raw', (S / (S + V)).toFixed(2), ' corr-scale', (Sc / (Sc + Vc)).toFixed(2));
}
