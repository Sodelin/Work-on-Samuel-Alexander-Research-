"""Exact, dependency-free NANUQ fixture for the canonical six-leaf level-2 bloblet.

Own calculation, 2026-09-29.  Fractions are exact.  The metric sums over
unordered witness pairs and uniformly averages DISTINCT quartet topologies.
Running writes JSON and Markdown only beside this script.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json

LEAVES = ['a1', 'c1', 'b1', 'b2', 'c2', 'a2']
ROOTED = [('r','u'), ('r','v'), ('u','pA1'), ('u','pA2'),
          ('v','pB1'), ('v','pB2'), ('pA1','a1'), ('pA1','h1'),
          ('pA2','a2'), ('pA2','h2'), ('pB1','b1'), ('pB1','h1'),
          ('pB2','b2'), ('pB2','h2'), ('h1','c1'), ('h2','c2')]

def canon_split(left, right):
    a, b = sorted(left), sorted(right)
    return (a, b) if (len(a), a) <= (len(b), b) else (b, a)

def split_name(split):
    return ','.join(split[0]) + '|' + ','.join(split[1])

def adjacency(edges):
    graph = {}
    for a,b in edges:
        graph.setdefault(a,set()).add(b)
        graph.setdefault(b,set()).add(a)
    return graph

def distance(graph, a, b):
    queue = deque([(a,0)])
    seen = {a}
    while queue:
        v,d = queue.popleft()
        if v == b:
            return d
        for w in graph[v] - seen:
            seen.add(w)
            queue.append((w,d+1))
    raise ValueError('disconnected')

def quartet(graph, taxa):
    a,b,c,d = sorted(taxa)
    pairings = [((a,b),(c,d)), ((a,c),(b,d)), ((a,d),(b,c))]
    sums = [distance(graph,*l) + distance(graph,*r) for l,r in pairings]
    minimum = min(sums)
    assert sums.count(minimum) == 1, (taxa, sums)
    return canon_split(*pairings[sums.index(minimum)])

def tree_splits(edges, leaves):
    result = set()
    graph = adjacency(edges)
    for a,b in edges:
        stack = [a]
        seen = {a}
        while stack:
            v = stack.pop()
            for w in graph[v]:
                if {v,w} == {a,b} or w in seen:
                    continue
                seen.add(w)
                stack.append(w)
        part = set(leaves) & seen
        if part and part != set(leaves):
            result.add(split_name(canon_split(part,set(leaves)-part)))
    return result

def metric(trees, leaves):
    graphs = [adjacency(edges) for edges in trees]
    rows = []
    distinct = {}
    for taxa in combinations(leaves,4):
        outcomes = [split_name(quartet(g,taxa)) for g in graphs]
        unique = sorted(set(outcomes))
        distinct[frozenset(taxa)] = [tuple(set(s.split(',')) for s in q.split('|')) for q in unique]
        rows.append({'taxa':sorted(taxa), 'switching_quartets':outcomes,
                     'multiplicities':dict(Counter(outcomes))})
    d = {x:{y:Fraction(0) for y in leaves} for x in leaves}
    dt = {x:{y:Fraction(0) for y in leaves} for x in leaves}
    for x,y in combinations(leaves,2):
        value = Fraction(2*len(leaves)-4)
        tilde = value
        for z,w in combinations([v for v in leaves if v not in (x,y)],2):
            qs = distinct[frozenset((x,y,z,w))]
            value += 2*Fraction(sum(not any({x,y} <= side for side in q) for q in qs),len(qs))
            qs_mult = [quartet(g,(x,y,z,w)) for g in graphs]
            tilde += 2*Fraction(sum(not any({x,y} <= set(side) for side in q) for q in qs_mult),len(qs_mult))
        d[x][y]=d[y][x]=value
        dt[x][y]=dt[y][x]=tilde
    return d,dt,rows

def alphas(d, order):
    n=len(order)
    answer=[]
    for i,j in combinations(range(n),2):
        a,b,c,e=order[i],order[(i+1)%n],order[j],order[(j+1)%n]
        split=canon_split(order[i+1:j+1],order[:i+1]+order[j+1:])
        value=d[a][c]+d[b][e]-d[a][e]-d[b][c]
        answer.append({'i':i,'j':j,'split':split_name(split),'alpha':value})
    return answer

def stringify(value):
    if isinstance(value,Fraction):
        return str(value)
    if isinstance(value,dict):
        return {k:stringify(v) for k,v in value.items()}
    if isinstance(value,(list,tuple)):
        return [stringify(v) for v in value]
    return value

def main():
    indegree=Counter(b for a,b in ROOTED)
    outdegree=Counter(a for a,b in ROOTED)
    vertices=set(indegree)|set(outdegree)
    assert (indegree['r'],outdegree['r'])==(0,2)
    assert all((indegree[x],outdegree[x])==(1,0) for x in LEAVES)
    assert all((indegree[x],outdegree[x])==(2,1) for x in ['h1','h2'])
    assert all((indegree[x],outdegree[x])==(1,2) for x in vertices-set(LEAVES)-{'r','h1','h2'})
    topological=['r','u','v','pA1','pA2','pB1','pB2','h1','h2']+LEAVES
    assert all(topological.index(a)<topological.index(b) for a,b in ROOTED)
    # r is LSA: its distinct outgoing subtrees contain a1 and b1, with unique root paths.
    assert indegree['a1']==indegree['pA1']==indegree['u']==1
    assert indegree['b1']==indegree['pB1']==indegree['v']==1
    semidirected=[e for e in ROOTED if 'r' not in e]+[('u','v')]
    trees=[]
    switchings=[]
    for choices in product('AB',repeat=2):
        deleted=[('p'+('B' if side=='A' else 'A')+str(i),'h'+str(i))
                 for i,side in enumerate(choices,1)]
        edges=[e for e in semidirected if e not in deleted]
        graph=adjacency(edges)
        assert len(edges)==len(graph)-1
        assert all(distance(graph,LEAVES[0],x)>0 for x in LEAVES[1:])
        trees.append(edges)
        switchings.append({'name':''.join(choices),'deleted_hybrid_edges':deleted,
                           'edges_before_suppression':edges,
                           'nontrivial_splits':sorted(s for s in tree_splits(edges,LEAVES)
                                                        if min(map(lambda x:len(x.split(',')),s.split('|')))>1)})
    d,dt,quartets=metric(trees,LEAVES)
    alpha=alphas(d,LEAVES)
    all_splits=set().union(*(tree_splits(t,LEAVES) for t in trees))
    assert all(x['alpha']>=0 for x in alpha)
    assert {x['split'] for x in alpha if x['alpha']>0}==all_splits
    for x,y in combinations(LEAVES,2):
        reconstructed=sum(a['alpha']/2 for a in alpha if (x in a['split'].split('|')[0].split(',')) != (y in a['split'].split('|')[0].split(',')))
        assert reconstructed==d[x][y]
    data={'description':'Rooted binary LSA partner of canonical six-leaf strict level-2 galled outer-labeled planar bloblet',
          'leaf_order':LEAVES,'rooted_edges':ROOTED,
          'semi_directed_edges':semidirected,'directed_hybrid_edges':[e for e in semidirected if e[1] in ('h1','h2')],
          'switching_order':['AA','AB','BA','BB'],'switchings':switchings,
          'quartets':quartets,'nanuq_distance':d,'multiplicity_averaged_distance':dt,
          'epsilon':{x:{y:d[x][y]-dt[x][y] for y in LEAVES} for x in LEAVES},
          'circular_alphas':alpha}
    here=Path(__file__).resolve().parent
    (here/'six-leaf-fixture.json').write_text(json.dumps(stringify(data),indent=2)+'\n',encoding='utf-8')
    lines=['# Exact six-leaf fixture','',
           'Generated by fixture.py with exact rational arithmetic. These are original calculations, not a general theorem.','',
           'Circular leaf order: '+', '.join(LEAVES)+'. Switching columns keep A or B into h1, then h2.','',
           '| Taxa | AA | AB | BA | BB |', '|---|---|---|---|---|']
    for row in quartets:
        lines.append('| '+';'.join(row['taxa'])+' | '+' | '.join(q.replace('|',' / ') for q in row['switching_quartets'])+' |')
    lines+=['','NANUQ distance matrix (same order):','', '| | '+' | '.join(LEAVES)+' |', '|---|'+'---|'*len(LEAVES)]
    for x in LEAVES:
        lines.append('| '+x+' | '+' | '.join(str(d[x][y]) for y in LEAVES)+' |')
    lines+=['','Circular alpha values; coefficient in the split decomposition is alpha/2.','',
            '| i,j | Split | alpha |','|---|---|---|']
    for a in alpha:
        lines.append('| '+str((a['i'],a['j']))+' | '+a['split'].replace('|',' / ')+' | '+str(a['alpha'])+' |')
    (here/'six-leaf-fixture.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
    print(json.dumps({'quartets':len(quartets),'switchings':len(trees),'positive_alpha_count':sum(a['alpha']>0 for a in alpha),'zero_alpha_count':sum(a['alpha']==0 for a in alpha),'checks':'passed'},indent=2))

if __name__=='__main__':
    main()
