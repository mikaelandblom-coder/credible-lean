"""Numerical checks for notes/kmeans-bridge.md.

Units i with fixed true levels x_i and uncorrelated unbiased estimates X_i,
Var(X_i) = v_i, w_i = 1/v_i. A partition into at most k cohorts; cohort a
pools its units by inverse variance: Xbar_a, Var(Xbar_a) = 1/W_a.
Rules:  pool  -> predict x_i by Xbar_a
        cred  -> predict x_i by mu + z_a (Xbar_a - mu), z_a = tau2/(tau2 + 1/W_a)
Losses: _w = exposure-weighted sum_i w_i MSE_i,  _u = unweighted sum_i MSE_i.
Prints the examples of the note and a random sweep counting optimal
partitions that are not intervals of the sorted levels.

Run: python3 notes/kmeans_bridge.py   (standard library only)
"""
import math
import random


def labellings(n, k):
    """Labellings of n units with exactly k nonempty groups (canonical)."""
    def rec(i, lab, m):
        if i == n:
            if m == k:
                yield tuple(lab)
            return
        for a in range(min(m + 1, k)):
            lab.append(a)
            yield from rec(i + 1, lab, max(m, a + 1))
            lab.pop()
    yield from rec(0, [], 0)


def at_most(n, k):
    for kk in range(1, k + 1):
        yield from labellings(n, kk)


def loss(x, v, lab, rule, tau2=1.0, mu=0.0):
    L = 0.0
    for a in set(lab):
        G = [i for i, b in enumerate(lab) if b == a]
        W = sum(1 / v[i] for i in G)
        xbar = sum(x[i] / v[i] for i in G) / W
        z, m = (1.0, 0.0) if rule.startswith("pool") else (tau2 / (tau2 + 1 / W), mu)
        for i in G:
            mse = (z * xbar + (1 - z) * m - x[i]) ** 2 + z * z / W
            L += mse / v[i] if rule.endswith("_w") else mse
    return L


def is_interval(x, lab):
    seq = [lab[i] for i in sorted(range(len(x)), key=lambda i: x[i])]
    seen, prev = set(), None
    for a in seq:
        if a != prev:
            if a in seen:
                return False
            seen.add(a)
            prev = a
    return True


def best(x, v, k, rule, tau2=1.0, mu=0.0):
    Ls = {lab: loss(x, v, lab, rule, tau2, mu) for lab in at_most(len(x), k)}
    opt = min(Ls, key=Ls.get)
    itv = min((l for l in Ls if is_interval(x, l)), key=Ls.get)
    return opt, Ls[opt], itv, Ls[itv]


def show(name, x, v, k, rule, tau2=1.0, mu=0.0):
    opt, L, itv, Li = best(x, v, k, rule, tau2, mu)
    print(f"{name}: x={x} v={v} k<={k} tau2={tau2}")
    print(f"  optimum {opt} loss {L:.4f} (interval: {is_interval(x, opt)});"
          f" best interval partition {itv} loss {Li:.4f}")


def pool_w_identity(trials=200, seed=0):
    """sum_i w_i MSE_i = weighted k-means cost at the pooled means + #cohorts."""
    rnd = random.Random(seed)
    err = 0.0
    for _ in range(trials):
        n = rnd.randint(2, 6)
        x = [rnd.uniform(-2, 2) for _ in range(n)]
        v = [math.exp(rnd.uniform(-3, 3)) for _ in range(n)]
        lab = tuple(rnd.randrange(3) for _ in range(n))
        km = 0.0
        for a in set(lab):
            G = [i for i, b in enumerate(lab) if b == a]
            W = sum(1 / v[i] for i in G)
            xbar = sum(x[i] / v[i] for i in G) / W
            km += sum((x[i] - xbar) ** 2 / v[i] for i in G)
        err = max(err, abs(loss(x, v, lab, "pool_w") - km - len(set(lab))))
    return err


def sweep(rule, common, trials, seed):
    rnd = random.Random(seed)
    bad = 0
    for _ in range(trials):
        n = rnd.randint(3, 6)
        k = rnd.randint(2, min(3, n - 1))
        x = sorted(rnd.uniform(-2, 2) for _ in range(n))
        v = [1.0] * n if common else [math.exp(rnd.uniform(-3, 3)) for _ in range(n)]
        tau2, mu = math.exp(rnd.uniform(-2, 2)), rnd.uniform(-3, 3)
        if not is_interval(x, best(x, v, k, rule, tau2, mu)[0]):
            bad += 1
    return bad


if __name__ == "__main__":
    print("pool_w identity, max error:", pool_w_identity())
    show("cred_u", [-0.5, 0, 0.5], [16, 0.5, 16], 2, "cred_u", tau2=0.5)
    show("cred_w", [-0.5, 0, 0.5], [16, 4, 16], 2, "cred_w", tau2=1.0)
    show("pool_u", [-1, 0, 0.2, 0.25, 1.5], [16, 0.0625, 0.5, 4, 2], 2, "pool_u")
    print("non-interval optima in 2000 random cases (n<=6, k<=3):")
    for rule in ["pool_w", "pool_u", "cred_w", "cred_u"]:
        print(f"  {rule}: common V {sweep(rule, True, 2000, 1)},"
              f" unequal V {sweep(rule, False, 2000, 2)}")
