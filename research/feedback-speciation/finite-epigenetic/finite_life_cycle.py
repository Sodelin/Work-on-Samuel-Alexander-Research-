"""Exact N=1-per-deme finite lift of Planidin2025 supplementary life cycle.
This is a declared offspring-sampling extension, not the authors' source code.
All kernel entries are fractions. No Monte Carlo sampling is used.
"""
from fractions import Fraction as Q
from itertools import combinations_with_replacement, product
from pathlib import Path
import argparse, json, hashlib, time

GENOTYPES=list(combinations_with_replacement(range(4),2))
INDEX={g:i for i,g in enumerate(GENOTYPES)}
STATES=list(product(range(10),repeat=2))
# haplotype=2*E+B; genotype stores the phase of its two haplotypes.
def marked(g):
    return tuple(sorted(h|1 for h in g))
def marker_count(g):
    return (g[0]&1)+(g[1]&1)
def fitness(g,d,s):
    e=(g[0]//2)+(g[1]//2)
    wrong=(2-e) if d==0 else e
    return 1-s*wrong/2
def gametes(g,r):
    a,b=g
    out=[Q(0)]*4
    for h,w in [(a,(1-r)/2),(b,(1-r)/2),
                (2*(a//2)+(b&1),r/2),(2*(b//2)+(a&1),r/2)]:
        out[h]+=w
    return out
def mutate_haplotype(h,d,mu,phi):
    alpha=mu*(1+phi)
    beta=mu*(1-phi)
    if d==1: alpha,beta=beta,alpha
    flip=beta if h//2 else alpha
    return [(h,1-flip),(h^2,flip)]
def offspring(state,d,m,s,r,mu,phi,pulse=False):
    # Migration pools are deterministic convex combinations of current adults.
    # Finite drift enters at offspring sampling, not before selection.
    source=[(GENOTYPES[state[d]],1-m),(GENOTYPES[state[1-d]],m)]
    if pulse and d==1:
        source[1]=(marked(source[1][0]),source[1][1])
    weighted=[(g,w*fitness(g,d,s)) for g,w in source]
    normalizer=sum(w for g,w in weighted)
    if normalizer<=0: raise ValueError("nonpositive mean fitness")
    gam=[Q(0)]*4
    for g,w in weighted:
        for i,p in enumerate(gametes(g,r)): gam[i]+=w*p/normalizer
    # Mating, then epimutation, including linkage phase.
    out=[Q(0)]*10
    for a,b in product(range(4),repeat=2):
        pair_probability=gam[a]*gam[b]
        if not pair_probability: continue
        for aa,pa in mutate_haplotype(a,d,mu,phi):
            for bb,pb in mutate_haplotype(b,d,mu,phi):
                out[INDEX[tuple(sorted((aa,bb)))]]+=pair_probability*pa*pb
    if min(out)<0 or sum(out)!=1: raise ArithmeticError("invalid offspring law")
    return out
def row(state,m,s,r,mu,phi,pulse=False):
    first=offspring(state,0,m,s,r,mu,phi,pulse)
    second=offspring(state,1,m,s,r,mu,phi,pulse)
    out=[a*b for a in first for b in second]
    if min(out)<0 or sum(out)!=1: raise ArithmeticError("invalid transition row")
    return out
def kernel(params):
    return [row(state,*params) for state in STATES]
def boundary(i):
    counts=[marker_count(GENOTYPES[g]) for g in STATES[i]]
    return 0 if counts==[0,0] else 1 if counts==[2,2] else None
def solve_linear(matrix,rhs,exact=True):
    n=len(rhs)
    # Exact elimination is bounded at82unknowns. No approximate results are certified.
    rows=[list(matrix[i])+[rhs[i]] for i in range(n)]
    for c in range(n):
        piv=next((j for j in range(c,n) if rows[j][c]),None)
        if piv is None: raise ArithmeticError(("singular",c))
        rows[c],rows[piv]=rows[piv],rows[c]
        d=rows[c][c]
        rows[c]=[v/d for v in rows[c]]
        for j in range(c+1,n):
            v=rows[j][c]
            if v: rows[j]=[a-v*b for a,b in zip(rows[j],rows[c])]
    ans=[Q(0) if exact else 0.0 for _ in range(n)]
    for c in reversed(range(n)):
        ans[c]=rows[c][-1]-sum(rows[c][j]*ans[j] for j in range(c+1,n))
    return ans
def fixation(P,exact=True):
    transient=[i for i in range(100) if boundary(i) is None]
    A=[[Q(int(i==j))-P[i][j] for j in transient] for i in transient]
    b=[sum(P[i][j] for j in range(100) if boundary(j)==1) for i in transient]
    if not exact:
        A=[[float(v) for v in row] for row in A]; b=list(map(float,b))
    x=solve_linear(A,b,exact)
    result=[Q(boundary(i)) if boundary(i) is not None else 0 for i in range(100)]
    for i,v in zip(transient,x): result[i]=v
    if exact:
        if not all(0<=v<=1 for v in result): raise ArithmeticError("invalid solution")
        if not all(result[i]==sum(P[i][j]*result[j] for j in range(100)) for i in range(100)):
            raise ArithmeticError("harmonic certificate failed")
    return result
def pack(v):
    return str(v) if isinstance(v,Q) else float(v)
def run(m,s,r,mu,phi,exact):
    params=(m,s,r,mu,phi)
    started=time.time()
    P=kernel(params)
    f=fixation(P,exact)
    # Source secondary contact: locally adapted allopatric fixed adults, neutralbb.
    init=(INDEX[(2,2)],INDEX[(0,0)])
    pulse=row(init,*params,pulse=True)
    probability=sum(pulse[j]*f[j] for j in range(100))
    RI=1-probability/(m/2)
    result={"parameters":dict(zip(["m","s","r","mu","phi"],map(str,params))),
      "population":"one diploid per deme", "initialization":"secondary-contact fixed local backgrounds",
      "sampling":"independent final offspring sampling; deterministic preselection migration pools",
      "mode":"exact rational" if exact else "floating exploration of exact kernel",
      "fixation_probability":pack(probability),"RI":pack(RI),"seconds":time.time()-started,
      "states":100,"transientMarkerStates":82,
      "kernel":[[str(v) for v in row] for row in P] if exact else None,
      "pulse":[str(v) for v in pulse] if exact else None,
      "fixationCertificate":[str(v) for v in f] if exact else None}
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--m",default="1/4");p.add_argument("--s",default="1/2")
    p.add_argument("--r",default="1/2");p.add_argument("--mu",default="0")
    p.add_argument("--phi",default="1");p.add_argument("--exact",action="store_true")
    p.add_argument("--output")
    a=p.parse_args()
    params=list(map(Q,[a.m,a.s,a.r,a.mu,a.phi]))
    m,s,r,mu,phi=params
    if not (0<m<1 and 0<=s<1 and 0<=r<=Q(1,2) and 0<=mu<=Q(1,2) and -1<=phi<=1):
        raise ValueError("parameters outside declared domain")
    result=run(*params,a.exact)
    if a.output:
        Path(a.output).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k not in {"kernel","pulse","fixationCertificate"}},indent=2))

if __name__=="__main__":
    main()
