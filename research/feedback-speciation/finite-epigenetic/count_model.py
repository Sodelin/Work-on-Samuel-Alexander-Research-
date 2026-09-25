"""Free-recombination count kernel, independently cross-checked against 100-state life cycle.
All arithmetic is integer/Fraction. N=1 per deme; m=1/4, s=r=1/2.
"""
from fractions import Fraction as Q
from pathlib import Path
from math import lcm
import json
import finite_life_cycle as full

SIZE=81
def decode(x): return divmod(x,9)
def allele(g): return divmod(g,3)
def fit(g,d):
 a,b=allele(g)
 return 2+a if d==0 else 4-a
def gamete_counts(x,d,pulse=False):
 g0,g1=decode(x)
 local,other=(g0,g1) if d==0 else (g1,g0)
 a,b=allele(local);c,e=allele(other)
 if pulse and d==1: e=2
 w0=3*fit(local,d);w1=fit(other,d)
 R=[w0*([2-a,a][u])*([2-b,b][v])+w1*([2-c,c][u])*([2-e,e][v])
    for u in range(2) for v in range(2)]
 D=4*(w0+w1)
 assert sum(R)==D
 return R,D
def offspring_counts(x,d,epi,pulse=False):
 (u,v,w,z),D=gamete_counts(x,d,pulse)
 if epi:
  b0=(u+w)**2;b1=2*(u+w)*(v+z);b2=(v+z)**2
  out=[0]*9
  a=2 if d==0 else 0
  out[3*a:3*a+3]=[b0,b1,b2]
 else:
  out=[u*u,2*u*v,v*v,2*u*w,2*u*z+2*v*w,2*v*z,w*w,2*w*z,z*z]
 assert sum(out)==D*D
 return out,D*D
def row_counts(x,epi,pulse=False):
 A,dA=offspring_counts(x,0,epi,pulse)
 B,dB=offspring_counts(x,1,epi,pulse)
 return [a*b for a in A for b in B],dA*dB
def win(x): return all(g%3==2 for g in decode(x))
def loss(x):return all(g%3==0 for g in decode(x))
def count_genotype(g):return 3*sum(h//2 for h in g)+sum(h&1 for h in g)
COLLAPSE=[9*count_genotype(full.GENOTYPES[a])+count_genotype(full.GENOTYPES[b]) for a,b in full.STATES]
def verify(name,epi,root):
 data=json.loads((root/(name+"-exact.json")).read_text())
 hs=[None]*81
 for x,c in enumerate(data["fixationCertificate"]):
  i=COLLAPSE[x];c=Q(c)
  if hs[i] is None: hs[i]=c
  assert hs[i]==c
 # Full phased law aggregated over all fibres, from every phased state.
 for x,oldrow in enumerate(data["kernel"]):
  agg=[Q(0)]*81
  for y,v in enumerate(oldrow):agg[COLLAPSE[y]]+=Q(v)
  ns,d=row_counts(COLLAPSE[x],epi)
  assert agg==[Q(n,d) for n in ns],(name,"kernel",x)
 L=lcm(*(c.denominator for c in hs))
 H=[int(c*L) for c in hs]
 minterminal=Q(1)
 for x in range(81):
  ns,d=row_counts(x,epi)
  assert sum(ns)==d and all(n>=0 for n in ns)
  assert sum(n*h for n,h in zip(ns,H))==d*H[x]
  assert 0<=H[x]<=L
  if win(x):assert H[x]==L and all(n==0 for y,n in enumerate(ns) if not win(y))
  if loss(x):assert H[x]==0 and all(n==0 for y,n in enumerate(ns) if not loss(y))
  term=sum(n for y,n in enumerate(ns) if win(y) or loss(y))
  minterminal=min(minterminal,Q(term,d))
 ns,d=row_counts(54,epi,pulse=True)
 pulse=[Q(0)]*81
 for y,v in enumerate(data["pulse"]):pulse[COLLAPSE[y]]+=Q(v)
 assert pulse==[Q(n,d) for n in ns]
 p=Q(sum(n*h for n,h in zip(ns,H)),d*L)
 assert p==Q(data["fixation_probability"])
 return {"model":name,"states":81,"certificateDenominator":L,"certificateNumerators":H,
         "minimumTerminalMass":str(minterminal),"epsilonBound":"1/100",
         "fixationProbability":str(p),"RI":str(1-8*p),"phaseAggregationCheckedRows":100,
         "pulseNumerators":ns,"pulseDenominator":d,
         "rowDenominators":[row_counts(x,epi)[1] for x in range(81)]}
def main():
 root=Path(__file__).parent
 data={name:verify(name,epi,root) for name,epi in [("genetic",False),("epigenetic",True)]}
 for name,d in data.items():
  assert Q(d["minimumTerminalMass"])>=Q(d["epsilonBound"])
 (root/"count-certificates.json").write_text(json.dumps(data,indent=2)+"\n",encoding="utf-8")
 print(json.dumps({k:{q:v for q,v in d.items() if q not in
    {"certificateNumerators","pulseNumerators","rowDenominators"}} for k,d in data.items()},indent=2))
if __name__=="__main__":main()
