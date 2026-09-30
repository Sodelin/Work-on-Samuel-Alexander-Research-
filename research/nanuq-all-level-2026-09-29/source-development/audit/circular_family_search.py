"""Exact audit of uniform-distinct-quartet metrics on circular tree families.
This overapproximates network-displayed families; no network admissibility claim.
No external dependencies. All distances and alpha coefficients are integers here.
"""
from itertools import combinations
from collections import Counter
import json, time
from pathlib import Path

OUT = Path(__file__).parent

def canon(s, full):
    return s if s & 1 else full ^ s

def compatible(a, b, full):
    return any(x == 0 for x in (a & b, a & (full ^ b), (full ^ a) & b, (full ^ a) & (full ^ b)))

def setup(n):
    full = (1 << n) - 1
    circle_splits = set()
    for i, j in combinations(range(n), 2):
        circle_splits.add(canon(sum(1 << k for k in range(i+1, j+1)), full))
    internals = sorted(s for s in circle_splits if 1 < s.bit_count() < n-1)
    pendant = {canon(1 << i, full) for i in range(n)}
    trees = [frozenset(t) for t in combinations(internals, n-3)
             if all(compatible(a,b,full) for a,b in combinations(t,2))]
    qs = list(combinations(range(n), 4))
    qi = {q:i for i,q in enumerate(qs)}
    codes = []
    for t in trees:
        row=[]
        for q in qs:
            qm=sum(1 << a for a in q)
            vals=set()
            for s in t:
                a=s & qm
                if a.bit_count()!=2: continue
                side = a if a & (1 << q[0]) else qm ^ a
                partner=next(k for k in q[1:] if side & (1 << k))
                vals.add(1 << (q.index(partner)-1))
            assert len(vals)==1
            row.append(vals.pop())
        codes.append(tuple(row))
    return full, trees, pendant, qs, qi, codes

def rho2(q, state, a, b):
    vals=[]
    for i in range(3):
        if state & (1<<i):
            pair={q[0],q[i+1]}
            vals.append(0 if ((a in pair)==(b in pair)) else 2)
    # Circular-compatible trees give at most two distinct quartets.
    assert len(vals) in (1,2)
    assert sum(vals) % len(vals)==0
    return sum(vals)//len(vals)

def distance(n, qs, states):
    d=[[0 if a==b else 2*n-4 for b in range(n)] for a in range(n)]
    for q,st in zip(qs,states):
        for a,b in combinations(q,2):
            x=rho2(q,st,a,b)
            d[a][b]+=x
            d[b][a]+=x
    return d

def alpha(d, order):
    n=len(order); full=(1<<n)-1
    ans={}
    for i,j in combinations(range(n),2):
        a,b,c,e=order[i],order[(i+1)%n],order[j],order[(j+1)%n]
        key=canon(sum(1<<order[k] for k in range(i+1,j+1)),full)
        ans[key]=d[a][c]+d[b][e]-d[a][e]-d[b][c]
    return ans

def clone_distance(n, d, qs, qi, states, v):
    e=[[0]*(n+1) for _ in range(n+1)]
    for a,b in combinations(range(n),2):
        if v in (a,b): x=d[a][b]+2*n-2
        else:
            x=d[a][b]+2
            for z in range(n):
                if z in (a,b,v): continue
                q=tuple(sorted((a,b,v,z)))
                x+=rho2(q,states[qi[q]],a,b)
        e[a][b]=e[b][a]=x
    for a in range(n):
        x=2*n-2 if a==v else e[a][v]
        e[a][n]=e[n][a]=x
    return e

def clone_support(support,n,v):
    full=(1<<(n+1))-1
    return {canon(s | ((1<<n) if s & (1<<v) else 0), full) for s in support} | {canon(1<<v,full),canon(1<<n,full)}

def show(s,n): return [i for i in range(n) if s & (1<<i)]

def run(n):
    start=time.time()
    full,trees,pendant,qs,qi,codes=setup(n)
    states=[None]*(1<<len(trees)); supports=[None]*len(states)
    states[0]=tuple(0 for _ in qs); supports[0]=pendant
    counts=Counter(); examples={}
    for fam in range(1,len(states)):
        bit=fam & -fam; ti=bit.bit_length()-1; rest=fam^bit
        st=tuple(a|b for a,b in zip(states[rest],codes[ti])); states[fam]=st
        support=supports[rest] | trees[ti]; supports[fam]=support
        d=distance(n,qs,st); aa=alpha(d,list(range(n)))
        bad={s:x for s,x in aa.items() if x<0 or ((x>0)!=(s in support))}
        counts['families']+=1
        if bad:
            counts['base_failure']+=1
            if 'base_failure' not in examples:
                examples['base_failure']={'family':[j for j in range(len(trees)) if fam>>j&1], 'alpha':{str(show(s,n)):x for s,x in bad.items()},'distance':d}
            continue
        counts['base_pass']+=1
        for v in range(n):
            dd=clone_distance(n,d,qs,qi,st,v)
            order=list(range(v+1))+[n]+list(range(v+1,n))
            expected=clone_support(support,n,v)
            ac=alpha(dd,order)
            badc={s:x for s,x in ac.items() if x<0 or ((x>0)!=(s in expected))}
            counts['clone_cases']+=1
            if badc:
                counts['clone_failure']+=1
                if 'clone_failure' not in examples:
                    examples['clone_failure']={'family':[j for j in range(len(trees)) if fam>>j&1], 'clone':v,'order':order,'alpha':{str(show(s,n+1)):x for s,x in badc.items()},'distance':dd,'original_distance':d}
            else: counts['clone_pass']+=1
    return {'n':n,'tree_count':len(trees),'trees':[[show(s,n) for s in sorted(t)] for t in trees], 'counts':dict(counts),'examples':examples,'elapsed_seconds':time.time()-start}

if __name__=='__main__':
    results=[run(n) for n in (4,5,6)]
    (OUT/'circular-family-search.json').write_text(json.dumps(results,indent=2)+'\n')
    for r in results:
        print(json.dumps({k:r[k] for k in ('n','tree_count','counts','examples','elapsed_seconds')}))
