"""Multi-blob controls and an independent up-down restriction route."""
from fractions import Fraction
from itertools import combinations, product
import json
from pathlib import Path

import exact_networks as en


def direct_quartets(net, taxa):
    """Construct a restriction from the union of all semi-directed up-down paths.

    Ordinary edges are bidirected. A traversed hybrid arrow cannot be followed
    later by traversal against a hybrid arrow. No displayed global trees are used
    to construct the restricted graph.
    """
    adj = en.adjacency(net.edges)
    arrows = {(p,h) for h,ps in net.hybrids.items() for p in ps}
    restricted = set()
    def walk(v, end, seen, path, down):
        if v == end:
            restricted.update(path)
            return
        for w in adj[v] - seen:
            if (w,v) in arrows and down:
                continue
            walk(w, end, seen | {w}, path + [en.edge(v,w)], down or (v,w) in arrows)
    for x,y in combinations(taxa,2):
        walk(x,y,{x},[],False)
    active = {h:ps for h,ps in net.hybrids.items() if all(en.edge(p,h) in restricted for p in ps)}
    result = set()
    for choices in product((0,1),repeat=len(active)):
        es = restricted.copy()
        for (h,ps),choice in zip(active.items(),choices):
            es.remove(en.edge(ps[1-choice],h))
        tree = en.simplify_tree(es,set(taxa))
        splits = en.tree_splits(tree,set(taxa))
        result |= {s for s in splits if len(s)==2}
    return result


def main():
    rows=[]
    base=en.theta()
    nets=[base,en.cherry_at(base,'nc1','cc')]
    patterns=[(2,0,1,1),(0,2,0,2),(3,1,0,0),(1,1,1,1),(0,0,1,1),(1,0,1,0)]
    for i,pat in enumerate(patterns):
        for ordinary in (False,True):
            p=en.theta(pat,prefix=f'p{i}{ordinary}')
            c=en.theta(patterns[-1-i],prefix=f'c{i}{ordinary}')
            parent_leaf=next(x for x in sorted(p.leaves) if (not x.endswith(('c1','c2')))==ordinary)
            port=next(x for x in sorted(c.leaves) if not x.endswith(('c1','c2')))
            joined=en.graft(p,parent_leaf,c,port)
            nets.append(joined)
            if i<3:
                third=en.theta((1,0,0,1),prefix=f't{i}{ordinary}')
                third_port=next(x for x in sorted(third.leaves) if not x.endswith(('c1','c2')))
                attach=sorted(joined.leaves)[-1]
                nets.append(en.graft(joined,attach,third,third_port))
    restriction_checks=0
    for k,net in enumerate(nets):
        row=en.check(net)
        # All quartets for the first controls and first two-blob example.
        # A fixed bounded subset for the remaining larger cases.
        qs,_=en.quartet_system(net)
        selected=list(qs) if k<3 else list(qs)[:12]
        for q in selected:
            assert direct_quartets(net,q)==qs[q],(net.name,q,'restriction mismatch')
        restriction_checks+=len(selected)
        row['direct_up_down_restrictions']=len(selected)
        row['edge_list']=[list(e) for e in sorted(net.edges)]
        row['hybrid_parents']=net.hybrids
        rows.append(row)
    output=Path(__file__).with_name('composition-controls.json')
    receipt={'status':'PASS','cases':len(rows),'max_leaves':max(r['leaves'] for r in rows),
             'max_hybrids':max(r['hybrids'] for r in rows),
             'direct_up_down_restriction_checks':restriction_checks,
             'scope':'Finite controls; actual admission, direct quartet restrictions, global/local identity and exact support checked',
             'results':rows}
    output.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
    print(json.dumps({k:v for k,v in receipt.items() if k!='results'}))


if __name__=='__main__':
    main()
