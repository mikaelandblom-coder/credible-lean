"""Numerical checks for notes/crossed-2x2.md.

Cells j = (country, type), X_j = mu + theta_j + e_j with
theta = alpha A_country + beta B_type + gamma C_cell, so
Cov(theta) = L = a2 [same country] + b2 [same type] + g2 I,
and Cov(e) = S. Compares, by total MSE over the cells,
  full  = best linear unbiased predictor  mu^ 1 + L K^-1 (X - mu^ 1),
  blend = thesis form z_j X_j + (1 - z_j) mu^ with the best z_j (Core, eq. 26),
  naive = thesis form with z from L = tau2 I (cross terms ignored),
and checks the closed forms of the note.

Run: python3 notes/crossed_2x2.py   (needs numpy)
"""
import numpy as np


def level_cov(nc, nt, a2, b2, g2):
    """L for an nc x nt grid, cells ordered (country, type)."""
    Ic, It, Jc, Jt = np.eye(nc), np.eye(nt), np.ones((nc, nc)), np.ones((nt, nt))
    return a2 * np.kron(Ic, Jt) + b2 * np.kron(Jc, It) + g2 * np.eye(nc * nt)


def gls(K):
    """GLS weights b and s2 = Var(mu^)."""
    w = np.linalg.solve(K, np.ones(len(K)))
    return w / w.sum(), 1 / w.sum()


def loss(A, L, S):
    """Total MSE of pred = A X when rows of A sum to 1 (mu drops out)."""
    n = len(L)
    return np.trace((A - np.eye(n)) @ L @ (A - np.eye(n)).T + A @ S @ A.T)


def full_rule(L, S, obs=None):
    """BLUP of all levels from the observed cells `obs` (default: all)."""
    n = len(L)
    obs = list(range(n)) if obs is None else obs
    K = (L + S)[np.ix_(obs, obs)]
    b, _ = gls(K)
    B = np.outer(np.ones(len(obs)), b)
    A = np.outer(np.ones(n), b) + L[:, obs] @ np.linalg.inv(K) @ (np.eye(len(obs)) - B)
    out = np.zeros((n, n))
    out[:, obs] = A
    return out


def blend_rule(L, S, Lw=None):
    """Thesis blend, z_j = (Lw_jj - (Lw b)_j) / (K_jj - s2); Lw = working L."""
    Lw = L if Lw is None else Lw
    n = len(L)
    K = Lw + S
    b, s2 = gls(K)
    z = (np.diag(Lw) - Lw @ b) / (np.diag(K) - s2)
    return np.diag(z) + np.outer(1 - z, b), z


# ---- the 2 x 2 example of the note ----------------------------------------
a2, b2, g2, s2 = 1.0, 4.0, 0.5, 2.0
tau2 = a2 + b2 + g2
L, S = level_cov(2, 2, a2, b2, g2), s2 * np.eye(4)
cells = ["SE sport", "SE family", "NO sport", "NO family"]

lam = {"c": 2 * a2 + g2, "t": 2 * b2 + g2, "i": g2}
zk = {k: v / (v + s2) for k, v in lam.items()}
D = sum(lam.values())
z = D / (D + 3 * s2)

A_full = full_rule(L, S)
A_blend, z_num = blend_rule(L, S)
A_naive, z_naive = blend_rule(L, S, Lw=tau2 * np.eye(4))

print("2 x 2, a2=%g b2=%g g2=%g sigma2=%g" % (a2, b2, g2, s2))
print("  z_country=%.3f z_type=%.3f z_cell=%.3f | blend z=%.3f | naive z=%.3f"
      % (zk["c"], zk["t"], zk["i"], z, z_naive[0]))
print("  weights for SE sport (%s):" % ", ".join(cells))
print("    full ", np.round(A_full[0], 3))
print("    blend", np.round(A_blend[0], 3))

# closed forms: weights of the full rule, common z, losses
sgn = np.array([[1, 1, 1, 1], [1, 1, -1, -1], [1, -1, 1, -1], [1, -1, -1, 1]])
w_closed = (sgn.T @ np.array([1, zk["c"], zk["t"], zk["i"]])) / 4
assert np.allclose(A_full[0], w_closed)
assert np.allclose(z_num, z)
L_full = s2 + sum(v * s2 / (v + s2) for v in lam.values())
L_blend = s2 + 3 * s2 * z
assert np.isclose(loss(A_full, L, S), L_full)
assert np.isclose(loss(A_blend, L, S), L_blend)
assert np.isclose(L_blend - L_full, sum((v + s2) * (z - zk[k]) ** 2 for k, v in lam.items()))
L_naive = loss(A_naive, L, S)
print("  total MSE: raw %.3f | naive %.3f | blend %.3f | full %.3f"
      % (4 * s2, L_naive, L_blend, L_full))

# equal noise correlation rho: sigma2 -> sigma2 (1 - rho) in the three z's
rho = 0.4
Sr = s2 * ((1 - rho) * np.eye(4) + rho * np.ones((4, 4)))
zr = {k: v / (v + s2 * (1 - rho)) for k, v in lam.items()}
assert np.allclose(full_rule(L, Sr)[0], (sgn.T @ np.array([1, zr["c"], zr["t"], zr["i"]])) / 4)

# ---- a missing cell: no data for SE sport ----------------------------------
obs = [1, 2, 3]
A_miss = full_rule(L, S, obs)
print("  SE sport unobserved, weights on (%s):" % ", ".join(cells[1:]),
      np.round(A_miss[0, obs], 3))
err = A_miss[0] - np.eye(4)[0]
mse_miss = err @ L @ err + A_miss[0] @ S @ A_miss[0]
bm, _ = gls((L + S)[np.ix_(obs, obs)])
e0 = np.zeros(4); e0[obs] = bm; e0 -= np.eye(4)[0]
mse_mean = e0 @ L @ e0 + bm @ S[np.ix_(obs, obs)] @ bm
print("    MSE for SE sport: full %.3f | collective mean only %.3f" % (mse_miss, mse_mean))
# additive, noise-free limit: SE family + NO sport - NO family
A_lim = full_rule(level_cov(2, 2, a2, b2, 0.0), 1e-9 * np.eye(4), obs)
assert np.allclose(A_lim[0, obs], [1, 1, -1], atol=1e-6)

# ---- general grid: eigenvalues of L ----------------------------------------
nc, nt = 3, 4
Lg = level_cov(nc, nt, a2, b2, g2)
ev = np.sort(np.linalg.eigvalsh(Lg))
expect = np.sort([nt * a2 + nc * b2 + g2] + [nt * a2 + g2] * (nc - 1)
                 + [nc * b2 + g2] * (nt - 1) + [g2] * ((nc - 1) * (nt - 1)))
assert np.allclose(ev, expect)
# full rule = grand mean + shrunk country, type and interaction effects
rng = np.random.default_rng(0)
X = rng.normal(size=(nc, nt))
m, r, c = X.mean(), X.mean(1, keepdims=True), X.mean(0, keepdims=True)
zc, zt, zi = [v / (v + s2) for v in (nt * a2 + g2, nc * b2 + g2, g2)]
pred = m + zc * (r - m) + zt * (c - m) + zi * (X - r - c + m)
assert np.allclose(full_rule(Lg, s2 * np.eye(nc * nt)) @ X.ravel(), pred.ravel())

# ---- thesis model (L = tau2 I), correlated noise, J = 3: blend vs full -----
S3 = np.array([[2.0, 1.2, 0.0], [1.2, 1.0, 0.3], [0.0, 0.3, 3.0]])
L3 = 1.5 * np.eye(3)
gap3 = loss(blend_rule(L3, S3)[0], L3, S3) - loss(full_rule(L3, S3), L3, S3)
assert gap3 > 1e-6
print("thesis model, J = 3, correlated noise: blend - full = %.4f" % gap3)
print("all closed forms check")
