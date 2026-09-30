"""Exact checks of the representative-cluster identity in source-audit.md."""
from fractions import Fraction
from itertools import combinations
from pathlib import Path
import importlib.util
import json

from fixture import LEAVES, adjacency, metric, quartet, split_name, stringify
from anchor_audit import make_theta

def graft_comb(edges, leaf, size):
    if size==1:
        return list(edges),[leaf]
    incident=[e for e in edges if leaf in e]
    assert len(incident)==1
    a,b=incident[0]
    parent=b if a==leaf else a
    out=[e for e in edges if e!=incident[0]]
    labels=[leaf+'_'+str(i) for i in range(size)]
    previous=parent
    for k in range(size-1):
        node=leaf+'_g'+str(k)
        out.extend([(previous,node),(node,labels[k])])
        previous=node
    out.append((previous,labels[-1]))
    return out,labels

def rho_of_graphs(graphs,x,y,z,w):
    qs={split_name(quartet(g,(x,y,z,w))) for g in graphs}
    return Fraction(sum(not any({x,y}<=set(side.split(',')) for side in q.split('|')) for q in qs),len(qs))

def check_bridge(mass_list):
    order,trees=make_theta((1,1,1,1))
    basegraphs=[adjacency(t) for t in trees]
    masses=dict(zip(order,mass_list))
    grown=[]
    for tree in trees:
        es=list(tree)
        clusters={}
        for x in order:
            es,clusters[x]=graft_comb(es,x,masses[x])
        grown.append(es)
    allleaves=[v for x in order for v in clusters[x]]
    graphs=[adjacency(t) for t in grown]
    d,_,_=metric(grown,allleaves)
    reps={x:clusters[x][-1] for x in order}
    M=len(allleaves)
    H={}
    P={}
    for x in order:
        outside=reps[next(y for y in order if y!=x)]
        H[x]=sum((2*rho_of_graphs(graphs,reps[x],outside,z,w)
                  for z,w in combinations([v for v in clusters[x] if v!=reps[x]],2)),Fraction(0))
        P[x]=(masses[x]-1)*(M-masses[x]+1)+H[x]
    for x,y in combinations(order,2):
        rest=[z for z in order if z not in (x,y)]
        dm=2*sum((masses[z]*masses[w]*rho_of_graphs(basegraphs,x,y,z,w)
                  for z,w in combinations(rest,2)),Fraction(0))
        dm+=(masses[x]+masses[y])*sum(masses[z] for z in rest)
        assert d[reps[x]][reps[y]]==dm+P[x]+P[y],(x,y,masses)
    return {'core_order':order,'masses':mass_list,'expanded_taxa':M,'H':H,'pendant_potentials':P,'checked_pairs':15}

def compare_parent():
    path=Path(__file__).resolve().parent.parent/'exact_networks.py'
    spec=importlib.util.spec_from_file_location('parent_nanuq_readonly',path)
    parent=importlib.util.module_from_spec(spec)
    spec.loader.exec_module(parent)
    net=parent.theta((1,1,1,1))
    qs,_=parent.quartet_system(net)
    porder=net.validate()['circular_order']
    pd=parent.distance(qs,porder)
    order,trees=make_theta((1,1,1,1))
    d,_,_=metric(trees,order)
    rename={x:'n'+x for x in order}
    assert set(rename.values())==net.leaves
    for x,y in combinations(order,2):
        assert d[x][y]==pd[rename[x],rename[y]]
    graphs=[adjacency(t) for t in trees]
    checked=0
    for q in combinations(order,4):
        for x,y in combinations(q,2):
            z,w=[v for v in q if v not in (x,y)]
            assert rho_of_graphs(graphs,x,y,z,w)==parent.rho(qs,*map(rename.get,(x,y,z,w)))
            checked+=1
    return {'metric_pairs':15,'quartet_pair_rhos':checked,'status':'MATCH'}

def main():
    cases=[[2,1,1,1,1,1],[1,1,1,1,3,1],[2,3,1,2,1,1]]
    result={'scope':'Exact examples, accompanying the algebraic witness-partition proof',
            'cluster_examples':[check_bridge(m) for m in cases],
            'parent_six_leaf_comparison':compare_parent()}
    here=Path(__file__).resolve().parent
    (here/'cluster-bridge-check.json').write_text(json.dumps(stringify(result),indent=2)+'\n',encoding='utf-8')
    print(json.dumps(stringify(result),indent=2))

if __name__=='__main__':
    main()
