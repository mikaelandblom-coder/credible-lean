#!/usr/bin/env python3
"""Grouping cohorts when each group has its own collective mean and its own tau^2
(spatially clustered Fay-Herriot, literature §10p). Are optimal groups intervals of the
sorted levels? See notes/group-variances.md. Pure Python, brute force over labellings.

    python3 notes/group_variances.py
"""
import math, random
def gmin(f,a,b,it=60):
    g=(5**.5-1)/2
    c=b-g*(b-a); d=a+g*(b-a)
    for _ in range(it):
        if f(c)<f(d): b=d
        else: a=c
        c=b-g*(b-a); d=a+g*(b-a)
    x=(a+b)/2; return f(x)
def tmin(f):
    grid=[e/10 for e in range(-200,201)]
    vals=[(f(math.exp(l)),l) for l in grid]
    v,l=min(vals)
    r=gmin(lambda t:f(math.exp(t)),l-.1,l+.1)
    return min(v,r,f(0.0))

def labellings(n,k):
    # all labellings with exactly k nonempty groups, canonical (first occurrence order)
    def rec(i,lab,m):
        if i==n:
            if m==k: yield tuple(lab)
            return
        for g in range(min(m+1,k)):
            yield from rec(i+1,lab+[g],max(m,g+1))
    yield from rec(0,[],0)

def is_interval(theta,lab):
    order=sorted(range(len(theta)),key=lambda i:theta[i])
    seq=[lab[i] for i in order]
    seen=set();prev=None
    for g in seq:
        if g!=prev:
            if g in seen: return False
            seen.add(g);prev=g
    return True

# C1: oracle conditional MSE, group g picks m_g, tau2_g >= 0 to minimise sum_j u_j[z^2 D + (1-z)^2 (m-theta)^2]
def oracle_cost(th,D,u):
    def f(t2,ret=False):
        z=[t2/(t2+d) for d in D]
        w=[ui*(1-zi)**2 for ui,zi in zip(u,z)]
        m=sum(wi*t for wi,t in zip(w,th))/sum(w) if sum(w)>0 else 0
        return sum(ui*(zi**2*d+(1-zi)**2*(m-t)**2) for ui,zi,d,t in zip(u,z,D,th))
    # search tau2 on log grid + refine
    return tmin(f)

# C2: normal (marginal) log-lik of group: x_j ~ N(m, tau2 + D_j); maximise over m, tau2>=0
def negll(x,D):
    def f(t2):
        v=[t2+d for d in D]; w=[1/vi for vi in v]
        m=sum(wi*xi for wi,xi in zip(w,x))/sum(w)
        return 0.5*sum(math.log(2*math.pi*vi)+(xi-m)**2/vi for vi,xi in zip(v,x))
    return tmin(f)

def solve(th,D,u,k,crit):
    res=[]
    for lab in labellings(len(th),k):
        c=0
        for g in range(k):
            idx=[i for i in range(len(th)) if lab[i]==g]
            if crit=='oracle': c+=oracle_cost([th[i] for i in idx],[D[i] for i in idx],[u[i] for i in idx])
            else: c+=negll([th[i] for i in idx],[D[i] for i in idx])
        res.append((c,lab))
    res.sort()
    bi=min(r for r in res if is_interval(th,r[1]))
    return res[0],bi

def common_cost(th, D, lab, k, t2):
    """Own means, one common tau2: oracle cost (weighted k-means with weights (1 - z)^2)."""
    z = [t2 / (t2 + d) for d in D]; c = 0
    for g in range(k):
        idx = [i for i in range(len(th)) if lab[i] == g]
        w = [(1 - z[i]) ** 2 for i in idx]
        m = sum(w[a] * th[i] for a, i in enumerate(idx)) / sum(w)
        c += sum(z[i] ** 2 * D[i] + (1 - z[i]) ** 2 * (m - th[i]) ** 2 for i in idx)
    return c

if __name__ == "__main__":
    print("Counterexample, equal D = 1, k = 2:")
    th = [-5, -0.2, -0.1, 0, 0.1, 0.2, 5]; D = [1] * 7
    for crit in ["oracle", "ll"]:
        b, bi = solve(th, D, [1] * 7, 2, crit)
        print(f"  {crit:6s} best {b[0]:.4f} {b[1]}   best intervals {bi[0]:.4f} {bi[1]}")
    random.seed(1)
    gens = {
        "normal levels, equal D": lambda n: ([random.gauss(0, 1) for _ in range(n)], [1] * n),
        "two regimes (+-1.5), equal D": lambda n: ([random.choice([-1.5, 1.5]) + random.gauss(0, .5) for _ in range(n)], [.5] * n),
        "heavy tails (t3), equal D": lambda n: ([random.gauss(0, 1) / max(1e-3, (sum(random.gauss(0, 1) ** 2 for _ in range(3)) / 3) ** .5) for _ in range(n)], [1] * n),
        "normal levels, D spread": lambda n: ([random.gauss(0, 1) for _ in range(n)], [math.exp(random.uniform(-2, 2)) for _ in range(n)]),
    }
    print("Random cases, n = 7, k = 2 (share with a non-interval optimum):")
    for name, gen in gens.items():
        for crit in ["oracle", "ll"]:
            bad = 0; N = 150
            for _ in range(N):
                th, D = gen(7)
                b, bi = solve(th, D, [1] * 7, 2, crit)
                if not is_interval(th, b[1]) and bi[0] - b[0] > 1e-6 * max(1, abs(b[0])): bad += 1
            print(f"  {name:30s} {crit:6s} {bad}/{N}")
    print("Own means, one common tau2 (chosen jointly), D spread:")
    random.seed(2)
    grid = [math.exp(e / 8) for e in range(-48, 49)]; bad = 0; N = 300
    for _ in range(N):
        th = [random.gauss(0, 1) * random.choice([1, 3]) for _ in range(7)]
        D = [math.exp(random.uniform(-2, 2)) for _ in range(7)]
        best = min(common_cost(th, D, lab, 2, t) for lab in labellings(7, 2) for t in grid)
        bi = min(common_cost(th, D, lab, 2, t) for lab in labellings(7, 2) if is_interval(th, lab) for t in grid)
        if bi - best > 1e-9: bad += 1
    print(f"  non-interval optimum {bad}/{N}")

