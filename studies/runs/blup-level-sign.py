# Purpose: Finding 40. Exact check (rational arithmetic, dual numbers for d/dτ²) that the level part of
# the first-order cross term of the plug-in BLUP on corrBS's K̂ can be positive.
# For any pooled fit (data only through s = (P, Qn, B)) a level Lₚ enters only B, with weight
# mₚ = Wₚ(1 − Wₚ/W), so the level part of 2E[AⱼBⱼ] is 2κL Σₚ mₚ(dⱼₚ − δₚⱼ)∂dⱼₚ/∂B
# = (κL/c) d/dτ² ‖dⱼ − eⱼ‖²ₘ (dⱼ depends on B only through τ̂²; ∂τ̂²/∂B = 1/c).
# BS: ≤ 0 always (Cumulants.crossTerm_bs_level_nonpos). BLUP: positive in the world below.
# Search for such worlds: studies/blup-level-sign.js. Run: python3 studies/runs/blup-level-sign.py
from fractions import Fraction as F
class D:  # dual number a + b·ε
    def __init__(s,a,b=0): s.a=F(a); s.b=F(b)
    def __add__(s,o): o=o if isinstance(o,D) else D(o); return D(s.a+o.a,s.b+o.b)
    __radd__=__add__
    def __sub__(s,o): o=o if isinstance(o,D) else D(o); return D(s.a-o.a,s.b-o.b)
    def __rsub__(s,o): return D(o)-s
    def __mul__(s,o): o=o if isinstance(o,D) else D(o); return D(s.a*o.a,s.a*o.b+s.b*o.a)
    __rmul__=__mul__
    def __truediv__(s,o): o=o if isinstance(o,D) else D(o); return D(s.a/o.a,(s.b*o.a-s.a*o.b)/(o.a*o.a))
def solve(A,b):
    n=len(A); M=[row[:]+[b[i]] for i,row in enumerate(A)]
    for c in range(n):
        p=next(r for r in range(c,n) if M[r][c].a!=0); M[c],M[p]=M[p],M[c]
        for r in range(n):
            if r!=c:
                f=M[r][c]/M[c][c]; M[r]=[M[r][k]-f*M[c][k] for k in range(n+1)]
    return [M[i][n]/M[i][i] for i in range(n)]
def run(rw, rho, t2, j, P=F(1)):  # rw: square roots of volumes, rows = regions
    J=len(rw); w=[[x*x for x in r] for r in rw]; wt=[sum(r) for r in w]; W=sum(wt)
    S=[[sum(a*b for a,b in zip(rw[i],rw[k])) for k in range(J)] for i in range(J)]
    t=D(t2,1)
    K=[[D(P/wt[i])+t if i==k else D(rho*P*S[i][k]/(wt[i]*wt[k])) for k in range(J)] for i in range(J)]
    one=[D(1)]*J; uu=solve(K,one); tot=sum(uu,D(0)); b=[x/tot for x in uu]
    l=solve(K,[t if i==j else D(0) for i in range(J)]); s=sum(l,D(0))
    d=[l[i]+(1-s)*b[i] for i in range(J)]
    m=[x*(1-x/W) for x in wt]
    f=sum((m[p]*(d[p]-(1 if p==j else 0))*(d[p]-(1 if p==j else 0)) for p in range(J)),D(0))
    mse=sum((d[i]*K[i][k]*d[k] for i in range(J) for k in range(J)),D(0))-2*t*d[j]+t
    # level part per γL, relative: 2τ⁴ Σ m(d−δ)∂d/∂B / mse = τ⁴ (df/dt2)/c0 / mse
    c0=W-sum(x*x for x in wt)/W
    return f.b, t2*t2*f.b/c0/mse.a, [float(x.a) for x in d]
# J = 3, T = 2, σ² = 1 (pooled P), ρ = 0.99, τ² = 1/20, volumes the squares of rw, region j = 1.
rw=[[F(1,5),F(23,100)],[F(13,100),F(14,100)],[F(35),F(44)]]
df,rel,d=run(rw,F(99,100),F(1,20),1)
print("d/dτ² ‖d − e₁‖²ₘ =",float(df),"(exact, > 0:",df>0,")")
print("level part per unit γL, relative to the region's BLUP MSE: %+.4f%%" % (100*float(rel)))
print("weights", [round(x,4) for x in d])
