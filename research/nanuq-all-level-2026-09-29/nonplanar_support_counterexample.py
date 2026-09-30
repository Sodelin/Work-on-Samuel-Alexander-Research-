"""Exact check of the received four-taxon non-outer-labeled counterexample."""
from collections import deque
from fractions import Fraction
from hashlib import sha256
from itertools import combinations, product
from pathlib import Path
import json

leaves = ('a', 'b', 'c', 'd')
edges = [('r','a'),('r','u'),('u','v'),('v','w'),('u','z'),('v','b'),
         ('w','hc'),('z','hc'),('hc','c'),('w','hd'),('z','hd'),('hd','d')]
vertices = {v for e in edges for v in e}
incoming = {v:[a for a,b in edges if b==v] for v in vertices}
outgoing = {v:[b for a,b in edges if a==v] for v in vertices}
for v in vertices:
    degree = (len(incoming[v]),len(outgoing[v]))
    expected = (0,2) if v=='r' else (1,0) if v in leaves else (2,1) if v in ('hc','hd') else (1,2)
    assert degree == expected, (v,degree,expected)
ready = deque(v for v in vertices if not incoming[v]); seen=[]
indeg = {v:len(incoming[v]) for v in vertices}
while ready:
    v=ready.popleft(); seen.append(v)
    for w in outgoing[v]:
        indeg[w]-=1
        if indeg[w]==0: ready.append(w)
assert len(seen)==len(vertices)
def reachable(omit=None):
    found={'r'}; todo=['r']
    while todo:
        for w in outgoing[todo.pop()]:
            if w!=omit and w not in found: found.add(w); todo.append(w)
    return found
assert all(x in reachable() for x in leaves)
assert all(any(x in reachable(v) for x in leaves) for v in vertices if v!='r')
assert all((u,v) in edges or (v,u) in edges for u,v in zip(('w','v','u'),('v','u','z')))
rows=[]; topologies=set()
for pc,pd in product(('w','z'),repeat=2):
    chosen=[e for e in edges if e[1] not in ('hc','hd') or e==(pc,'hc') or e==(pd,'hd')]
    graph={v:[] for v in vertices}
    for u,v in chosen: graph[u].append(v); graph[v].append(u)
    dist={}
    for x in leaves:
        d={x:0};todo=deque([x])
        while todo:
            v=todo.popleft()
            for w in graph[v]:
                if w not in d: d[w]=d[v]+1;todo.append(w)
        assert len(d)==len(vertices) and len(chosen)==len(vertices)-1
        for y in leaves:dist[x,y]=d[y]
    pairs=((('a','b'),('c','d')),(('a','c'),('b','d')),(('a','d'),('b','c')))
    values=[sum(dist[x,y] for x,y in pairing) for pairing in pairs]
    best=min(range(3),key=values.__getitem__)
    assert sorted(values)[0]<sorted(values)[1]==sorted(values)[2]
    split=frozenset(pairs[best][0]);topologies.add(split)
    rows.append({'parents':[pc,pd],'quartet':''.join(pairs[best][0])+'|'+''.join(pairs[best][1]),'four_point_sums':values})
assert len(topologies)==3
distances={}
for x,y in combinations(leaves,2):
    rho=Fraction(sum((x in s)!=(y in s) for s in topologies),len(topologies))
    d=4+2*rho
    assert rho==Fraction(2,3) and d==Fraction(16,3)
    distances[x+y]=str(d)
report={'status':'PASS','source_sha256':sha256(Path(__file__).read_bytes()).hexdigest(),
        'rooted_binary_DAG':True,'root_is_LSA':True,'hybrids':2,
        'switchings':rows,'distinct_topologies':3,'distances':distances,
        'conclusion':'Exact displayed-split support fails when outer-labeled planarity is omitted; circularity itself is not falsified.',
        'scope':'Direct finite graph and exact arithmetic check; no proof-assistant verification.'}
Path(__file__).with_name('nonplanar-support-counterexample.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8',newline='\n')
print(json.dumps(report))
