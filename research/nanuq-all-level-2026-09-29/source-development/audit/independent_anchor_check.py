"""Independent exact checker for anchor-alpha signs on canonical theta bloblets.
Constructs the four switched trees directly, reads their quartet topology from
six graph distances via the four-point condition, and evaluates integer alphas.
Does not import the parent's checker or use its split/suppression procedures.
"""
from itertools import combinations, product
from collections import deque, Counter
from pathlib import Path
import json, hashlib, time

OUT=Path(__file__).parent

def label(arm,j): return 'n'+arm+'l'+str(j)

def circular(counts):
    a1,b1,a2,b2=counts
    return ['nc1']+[label('b1',j) for j in reversed(range(b1))]+[label('b2',j) for j in range(b2)]+['nc2']+[label('a2',j) for j in reversed(range(a2))]+[label('a1',j) for j in range(a1)]

def tree_metric(counts, choices):
    adj={}
    def add(a,b):
        adj.setdefault(a,set()).add(b);adj.setdefault(b,set()).add(a)
    add('U','V');ends={}
    for arm,count in zip(('a1','b1','a2','b2'),counts):
        prev='U' if arm[0]=='a' else 'V'
        for j in range(count):
            node=arm+'_'+str(j)
            add(prev,node);add(node,label(arm,j));prev=node
        ends[arm]=prev
    for i,ch in enumerate(choices,1): add(ends[('a' if ch==0 else 'b')+str(i)],'nc'+str(i))
    assert sum(map(len,adj.values()))//2==len(adj)-1
    leaves=circular(counts)
    result={}
    for leaf in leaves:
        todo=deque([leaf]);dist={leaf:0}
        while todo:
            a=todo.popleft()
            for b in adj[a]:
                if b not in dist:dist[b]=dist[a]+1;todo.append(b)
        assert len(dist)==len(adj)
        for other in leaves: result[leaf,other]=dist[other]
    return result

def quartets(counts):
    order=circular(counts); metrics=[tree_metric(counts,ch) for ch in product((0,1),repeat=2)]
    out={}
    for q in combinations(sorted(order),4):
        a,b,c,d=q; pairings=(((a,b),(c,d)),((a,c),(b,d)),((a,d),(b,c)))
        seen=set()
        for metric in metrics:
            scores=[sum(metric[x,y] for x,y in pairing) for pairing in pairings]
            best=min(scores); assert scores.count(best)==1
            seen.add(tuple(pairings[scores.index(best)][0]))
        assert 1<=len(seen)<=2
        out[q]=frozenset(seen)
    return out

def rho2(qs,x,y,p,q):
    splits=qs[tuple(sorted((x,y,p,q)))]
    numerator=2*sum((x in s)!=(y in s) for s in splits)
    assert numerator%len(splits)==0
    return numerator//len(splits)

def anchor(qs,x,y,p,q):
    if x==y:return 0
    if {x,y}=={p,q}:return 0
    if {x,y}&{p,q}:return 1
    return rho2(qs,x,y,p,q)

def alpha_value(dist,order,i,j):
    a,b,c,d=order[i],order[(i+1)%len(order)],order[j],order[(j+1)%len(order)]
    return dist(a,c)+dist(b,d)-dist(a,d)-dist(b,c)

def check(counts):
    order=circular(counts);qs=quartets(counts);n=len(order)
    hist=Counter(); checks=0; negative=[]
    for p,q in combinations(order,2):
        for i,j in combinations(range(n),2):
            v=alpha_value(lambda x,y:anchor(qs,x,y,p,q),order,i,j)
            hist[v]+=1;checks+=1
            if v<0:negative.append({'anchors':[p,q],'indices':[i,j],'value':v})
    # Independent algebraic identity check at nonuniform positive integer masses.
    masses={x:i+1 for i,x in enumerate(order)}
    for x,y in combinations(order,2):
        expected=sum(masses[p]*masses[q]*anchor(qs,x,y,p,q) for p,q in combinations(order,2))
        rest=[a for a in order if a not in (x,y)]
        expanded=sum(masses[p]*masses[q]*rho2(qs,x,y,p,q) for p,q in combinations(rest,2))+(masses[x]+masses[y])*sum(masses[p] for p in rest)
        assert expected==expanded
    return {'counts':counts,'leaves':n,'checks':checks,'histogram':dict(sorted(hist.items())),'negative':negative}

def direct_family_clone_control():
    # Independently recompute the artificial-family witness after cloning, using
    # only the explicit split sets; do not use the derived clone-distance formula.
    family=[[{0,1},{0,1,5},{0,1,2,5}], [{0,1,2},{0,1,2,3},{0,3,4,5}], [{0,1,2,3},{0,4,5},{0,1,4,5}]]
    def matrix(trees,n):
        full=set(range(n));d=[[0 if x==y else 2*n-4 for y in range(n)] for x in range(n)]
        for q in combinations(range(n),4):
            qq=set(q);splits=set()
            for t in trees:
                induced=set()
                for side in t:
                    s=side & qq
                    if len(s)==2:
                        induced.add(frozenset(s if q[0] in s else qq-s))
                assert len(induced)==1
                splits|=induced
            for a,b in combinations(q,2):
                contribution=2*sum((a in s)!=(b in s) for s in splits)//len(splits)
                d[a][b]+=contribution;d[b][a]+=contribution
        return d
    rows=[]
    for n in (6,7,8):
        d=matrix(family,n)
        rows.append({'n':n,'alpha_23':d[1][3]+d[2][4]-d[1][4]-d[2][3],'distance':d})
        family=[[s|({n} if 0 in s else set()) for s in t]+[{0,n}] for t in family]
    assert [r['alpha_23'] for r in rows]==[1,0,-1]
    return rows

if __name__=='__main__':
    start=time.time()
    rows=[check(list(c)) for c in product(range(7),repeat=4) if 1<=sum(c)<=6]
    negatives=[r for r in rows if r['negative']]
    report={'status':'PASS' if not negatives else 'FAIL','method':'direct switched trees; graph-distance quartet four-point tests; integer coefficients','templates':len(rows),'anchor_checks':sum(r['checks'] for r in rows),'negative_templates':len(negatives),'artificial_clone_control':direct_family_clone_control(),'results':rows,'elapsed_seconds':time.time()-start}
    assert report['templates']==209 and report['anchor_checks']==100823
    report['source_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    (OUT/'independent-anchor-check.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:report[k] for k in ('status','templates','anchor_checks','negative_templates','elapsed_seconds','source_sha256')}))
