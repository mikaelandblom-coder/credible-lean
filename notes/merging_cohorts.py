"""Numerical checks for notes/merging-cohorts.md.

Two cohorts, X_j = mu + theta_j + e_j, Var(theta_j) = tau2,
cov(theta_1, theta_2) = phi * tau2, Cov(e) = Sigma (sigma_j^2, c = s1 s2 rho).
"Separate" = credibility rule designed for phi = 0 (the thesis, eq. 32),
"merged"   = rule designed for phi = 1 (mu_1 = mu_2).
Prints the threshold phi* above which merging has the lower total MSE,
for the pair alone (Case A, mu unknown) and inside a large portfolio
(Case B, mu known), and checks the closed forms of the note.

Run: python3 notes/merging_cohorts.py   (needs numpy)
"""
import numpy as np

I, E, u = np.eye(2), np.array([[0.0, 1.0], [1.0, 0.0]]), np.ones(2)


def loss(A, T, S):
    """Total MSE sum_j E(pred_j - mu_j)^2 of pred = mu u + A (X - mu u)."""
    return np.trace((A - I) @ T @ (A - I).T + A @ S @ A.T)


def rule_known_mu(Tw, S):
    """Case B: best linear predictor under working Cov(theta) = Tw, mu known."""
    return Tw @ np.linalg.inv(Tw + S)


def rule_unknown_mu(Tw, S):
    """Case A: GLS mean plus credibility correction (rows sum to 1)."""
    Ki = np.linalg.inv(Tw + S)
    P = np.outer(u, Ki @ u / (u @ Ki @ u))
    return P + Tw @ Ki @ (I - P)


def sigma(k1, k2, rho, tau2=1.0):
    s1, s2 = np.sqrt(k1 * tau2), np.sqrt(k2 * tau2)
    c = s1 * s2 * rho
    return np.array([[s1 * s1, c], [c, s2 * s2]])


def phi_star(rule, k1, k2, rho, tau2=1.0):
    """The loss is linear in phi: L = L0 + phi L1. Solve L(S) = L(M)."""
    S = sigma(k1, k2, rho, tau2)
    AS, AM = rule(tau2 * I, S), rule(tau2 * (I + E), S)
    L0 = lambda A: loss(A, tau2 * I, S)
    L1 = lambda A: tau2 * np.trace((A - I) @ E @ (A - I).T)
    return (L0(AM) - L0(AS)) / (L1(AS) - L1(AM))


def main():
    rng = np.random.default_rng(0)
    # 1. Case A closed form: merge iff d < V tau2 / (V + tau2), d = 2 tau2 (1 - phi).
    # 2. Case B closed form for equal sigma, rho = 0: phi* = (1 + z^2) / 2.
    # 3. Brute force: the threshold really separates the two regimes.
    bad = 0
    for _ in range(20000):
        k1, k2 = rng.uniform(0.05, 5, 2)
        rho, phi, tau2 = rng.uniform(-0.95, 0.95), rng.uniform(0, 1), rng.uniform(0.2, 3)
        S = sigma(k1, k2, rho, tau2)
        T = tau2 * (I + phi * E)
        V = S[0, 0] + S[1, 1] - 2 * S[0, 1]
        # thesis eq. (32): weight of cohort 2 in the predictor of cohort 1
        AS = rule_unknown_mu(tau2 * I, S)
        assert abs(AS[0, 1] - (S[0, 0] - S[0, 1]) / (V + 2 * tau2)) < 1e-9
        for rule in (rule_unknown_mu, rule_known_mu):
            merge = loss(rule(tau2 * (I + E), S), T, S) < loss(rule(tau2 * I, S), T, S)
            bad += merge != (phi > phi_star(rule, k1, k2, rho, tau2))
        d = 2 * tau2 * (1 - phi)
        merge_A = (loss(rule_unknown_mu(tau2 * (I + E), S), T, S)
                   < loss(rule_unknown_mu(tau2 * I, S), T, S))
        bad += merge_A != (d < V * tau2 / (V + tau2))
    for k in (0.1, 0.25, 1, 4, 10):
        z = 1 / (1 + k)
        assert abs(phi_star(rule_known_mu, k, k, 0.0) - (1 + z * z) / 2) < 1e-9
    print("brute-force mismatches:", bad)

    print("\nkappa1 kappa2   rho | phi* pair alone (A) | phi* in portfolio (B)")
    for k1, k2 in [(0.25, 0.25), (1, 1), (4, 4), (1, 16), (0.1, 10)]:
        for rho in (-0.5, 0.0, 0.5, 0.9):
            a = phi_star(rule_unknown_mu, k1, k2, rho)
            b = phi_star(rule_known_mu, k1, k2, rho)
            print(f"{k1:6} {k2:6} {rho:5} | {a:19.3f} | {b:21.3f}")

    lo, arg, nonmono = 9.0, None, 0
    for k1 in np.geomspace(0.01, 100, 25):
        for k2 in np.geomspace(0.01, 100, 25):
            vals = [phi_star(rule_known_mu, k1, k2, r) for r in np.linspace(-0.99, 0.99, 41)]
            if min(vals) < lo:
                lo, arg = min(vals), (round(float(k1), 1), round(float(k2), 1))
            nonmono += any(np.diff(vals) < -1e-12)
    print(f"\nCase B on kappa grid [0.01, 100]^2: min phi* = {lo:.3f} at kappa = {arg};"
          f" {nonmono}/625 kappa pairs not monotone in rho")


if __name__ == "__main__":
    main()
