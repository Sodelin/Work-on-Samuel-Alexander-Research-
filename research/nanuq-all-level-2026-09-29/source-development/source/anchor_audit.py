"""Independent exhaustive anchor check on the 205 reduced theta templates.

Quartets are extracted by four-point comparisons of graph path lengths, rather
than by the parent implementation's displayed-edge-split restriction.  This is
an exact finite computation; the separate reduction argument is mathematical.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path
import json

from fixture import adjacency, alphas, quartet, split_name, tree_splits, stringify

def make_theta(counts):
    edges=[('r','u'),('r','v')]
    arms={}
    parents={}
    for label,start,end,count in zip(('a1','b1','a2','b2'),('u','v','u','v'),('h1','h1','h2','h2'),counts):
        previous=start
        arms[label]=[]
        for k in range(count):
            node=label+'n'+str(k)
            leaf=label+'l'+str(k)
            arms[label].append(leaf)
            edges.extend([(previous,node),(node,leaf)])
            previous=node
        edges.append((previous,end))
        parents[label]=(previous,end)
    edges.extend([('h1','c1'),('h2','c2')])
    order=arms['a1']+['c1']+arms['b1'][::-1]+arms['b2']+['c2']+arms['a2'][::-1]
    trees=[]
    for first,second in product('ab',repeat=2):
        deleted=[parents[('b' if first=='a' else 'a')+'1'],parents[('b' if second=='a' else 'a')+'2']]
        tree=[e for e in edges if e not in deleted]
        g=adjacency(tree)
        assert len(tree)==len(g)-1
        trees.append(tree)
    return order,trees

def check(counts):
    order,trees=make_theta(counts)
    graphs=[adjacency(t) for t in trees]
    qsets={}
    for q in combinations(order,4):
        topologies={split_name(quartet(g,q)) for g in graphs}
        assert 1<=len(topologies)<=2
        qsets[frozenset(q)]=[tuple(set(side.split(',')) for side in s.split('|')) for s in topologies]
    support=set().union(*(tree_splits(t,order) for t in trees))
    anchor_support=set()
    values=Counter()
    coefficients_checked=0
    for p,q in combinations(order,2):
        d={x:{y:Fraction(0) for y in order} for x in order}
        for x,y in combinations(order,2):
            if {x,y}=={p,q}:
                value=Fraction(0)
            elif {x,y}&{p,q}:
                value=Fraction(1)
            else:
                quartets=qsets[frozenset((x,y,p,q))]
                value=2*Fraction(sum(not any({x,y}<=side for side in z) for z in quartets),len(quartets))
            d[x][y]=d[y][x]=value
        for a in alphas(d,order):
            coefficients_checked+=1
            assert a['alpha']>=0, (counts,p,q,a)
            assert a['alpha']==0 or a['split'] in support, (counts,p,q,a,'support')
            values[str(a['alpha'])]+=1
            if a['alpha']>0:
                anchor_support.add(a['split'])
    assert anchor_support==support, (counts,'missing support',support-anchor_support)
    return {'arm_counts_a1_b1_a2_b2':counts,'leaves':len(order),'anchor_pairs':len(order)*(len(order)-1)//2,
            'coefficients_checked':coefficients_checked,'coefficient_histogram':dict(values),
            'displayed_split_count':len(support),'support_union_matches':True}

def main():
    rows=[check(counts) for counts in product(range(7),repeat=4) if 2<=sum(counts)<=6]
    assert len(rows)==205
    total=Counter()
    for row in rows:
        total.update(row['coefficient_histogram'])
    receipt={'status':'PASS_EXACT_FINITE_ANCHOR_CHECK',
             'scope':'All nonnegative arm-count quadruples with total between 2 and 6; four-point tree-distance quartet extraction',
             'templates':len(rows),'anchor_pairs':sum(r['anchor_pairs'] for r in rows),
             'coefficients_checked':sum(r['coefficients_checked'] for r in rows),
             'coefficient_histogram':dict(total),'results':rows}
    here=Path(__file__).resolve().parent
    (here/'anchor-audit.json').write_text(json.dumps(stringify(receipt),indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'},indent=2))

if __name__=='__main__':
    main()
