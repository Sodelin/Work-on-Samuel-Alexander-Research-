from fractions import Fraction
from hashlib import sha256
from importlib.util import spec_from_file_location, module_from_spec
from itertools import combinations, product
from pathlib import Path
import json

root=Path(r'C:/Users/Owner/Documents/Codex/2026-09-29/vibemathed-biology/adjacent-nanuq')
out=Path(__file__).resolve().parent

def load(name):
    spec=spec_from_file_location(name,root/(name+'.py'))
    mod=module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod
screen=load('all_level_screen')
independent=load('independent_all_level_check')
domain=json.loads((root/'parameter-domain.json').read_text())
saved=json.loads((root/'independent-all-level-check.json').read_text())
w=next(row['witness'] for row in domain['inequalities'] if row['row']==[0,-1,0,1,0])
assert w=={'taxa':5,'duplication_mask':1,'pattern':4717,'anchors':[0,1],'gaps':[2,4]}
tips,qs,patterns=screen.systems(w['taxa'],w['duplication_mask'])
tree=patterns[w['pattern']]
locations=tuple(tuple(i for i,label in enumerate(tips) if label==x) for x in range(5))
distance=independent.leaf_distances(tree,len(tips))
codes,choices=independent.global_choice_system(distance,locations,qs)
packed=sum(code << (3*k) for k,code in enumerate(codes))
assert packed==w['pattern']
params={'c':Fraction(1),'s':Fraction(1),'a':Fraction(1,2),'o':Fraction(1)}

def entry(x,y,p,q,data):
    if x==y or {x,y}=={p,q}: return Fraction(0),'zero'
    if {x,y}&{p,q}: return Fraction(1),'anchor_incidence'
    Q=tuple(sorted((x,y,p,q)))
    code=data[Q]
    assert code in (1,4,5)
    if code==5:
        category='o' if abs(Q.index(x)-Q.index(y))==2 else 'a'
    else:
        side={Q[0],Q[1]} if code==1 else {Q[0],Q[3]}
        category='c' if ((x in side)==(y in side)) else 's'
    return 2*params[category],category

def alpha(n,system,p,q,i,j):
    data=dict(zip(combinations(range(n),4),system))
    pairs=((i,j),((i+1)%n,(j+1)%n),(i,(j+1)%n),((i+1)%n,j))
    terms=[entry(x,y,p,q,data) for x,y in pairs]
    value=terms[0][0]+terms[1][0]-terms[2][0]-terms[3][0]
    return value,pairs,terms

small=[]
for row in saved['rows']:
    n=row['taxa']
    if n>4: continue
    values=[]
    for system in row['quartet_systems']:
        for p,q in combinations(range(n),2):
            for i,j in combinations(range(n),2):
                values.append(alpha(n,system,p,q,i,j)[0])
    assert min(values)>=0
    small.append({'taxa':n,'systems':len(row['quartet_systems']),'coefficients':len(values),
                  'minimum':str(min(values)),'all_nonnegative':True})
value,pairs,terms=alpha(5,codes,*w['anchors'],*w['gaps'])
assert value==Fraction(-1)
report={'status':'PASS_FOCUSED_FIVE_TAXON_OBSTRUCTION','parameters':{k:str(v) for k,v in params.items()},
 'four_taxon_certificate_passes':small,'witness':w,'expanded_tip_labels':list(tips),
 'rooted_plane_tree':[0,tree],'rooted_subtree':tree,'global_copy_choices_checked':choices,
 'independent_quartet_codes':list(codes),'reconstructed_packed_pattern':packed,
 'terms':[{'pair':list(pair),'entry':str(term[0]),'category':term[1]}
          for pair,term in zip(pairs,terms)],
 'coefficient':str(value),'raw_symbolic_coefficient':'2*a - 2*c','normalized_row':[0,-1,0,1,0],
 'scope':'Actual saved paired-tip representation. Counterexample to reducing universal anchor-positivity parameter checks to at most four total taxa. Not a counterexample at original NANUQ scores, nor a proof that six rather than five is minimal.',
 'inputs':{name:sha256((root/name).read_bytes()).hexdigest() for name in
           ('all_level_screen.py','independent_all_level_check.py','parameter-domain.json','independent-all-level-check.json')}}
(out/'FOUR-TAXON-OBSTRUCTION.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))