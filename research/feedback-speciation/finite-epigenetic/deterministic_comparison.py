"""Direct deterministic Planidin diploid recursion; no averaging of a finite kernel.
Fixed secondary contact m=1/4, s=r=1/2, genetic versus pure induction.
Decimal diagnostics are numerical checks, not a rigorous enclosure.
"""
from decimal import Decimal, localcontext
from itertools import combinations_with_replacement
from fractions import Fraction
from pathlib import Path
import json

GENOTYPES = list(combinations_with_replacement(range(4), 2))
INDEX = {g:i for i,g in enumerate(GENOTYPES)}

def one_generation(adults, pure_induction, pulse=False, number=Decimal):
    D=number; one=D(1); half=one/2; m=one/4
    result=[]
    for deme in range(2):
        pool=[(1-m)*v for v in adults[deme]]
        for i,(a,b) in enumerate(GENOTYPES):
            destination=INDEX[tuple(sorted((a|1,b|1)))] if pulse and deme==1 else i
            pool[destination]+=m*adults[1-deme][i]
        weighted=[]
        for mass,(a,b) in zip(pool,GENOTYPES):
            e=a//2+b//2
            wrong=2-e if deme==0 else e
            weighted.append(mass*(one-D(wrong)/4))
        total=sum(weighted)
        gam=[D(0)]*4
        for mass,(a,b) in zip(weighted,GENOTYPES):
            normalized=mass/total
            # r=1/2: parental and recombinant haplotypes each contribute1/4.
            for h in [a,b,2*(a//2)+(b&1),2*(b//2)+(a&1)]:
                gam[h]+=normalized/4
        offspring=[D(0)]*10
        for a in range(4):
            for b in range(4):
                aa,bb=a,b
                if pure_induction:
                    aa=(a&1)+(2 if deme==0 else 0)
                    bb=(b&1)+(2 if deme==0 else 0)
                offspring[INDEX[tuple(sorted((aa,bb)))]]+=gam[a]*gam[b]
        if number is Fraction:
            assert sum(offspring)==one
        else:
            assert abs(sum(offspring)-one)<D(10)**(-max(10,__import__('decimal').getcontext().prec-5))
        assert min(offspring)>=0
        result.append(offspring)
    return result

def marker(adults):
    return [sum(v*Decimal((a&1)+(b&1))/2 for v,(a,b) in zip(row,GENOTYPES)) for row in adults]

def background(adults):
    return [sum(v*Decimal(a//2+b//2)/2 for v,(a,b) in zip(row,GENOTYPES)) for row in adults]

def trajectory(pure_induction, precision, horizon):
    with localcontext() as ctx:
        ctx.prec=precision
        adults=[[Decimal(0)]*10 for _ in range(2)]
        adults[0][INDEX[(2,2)]]=Decimal(1)
        adults[1][INDEX[(0,0)]]=Decimal(1)
        checkpoints=[]; old_ri=None
        for generation in range(1,horizon+1):
            new=one_generation(adults,pure_induction,pulse=generation==1)
            q=marker(new); B=sum(q)/2; RI=1-8*B
            maximum_change=max(abs(a-b) for row,nrow in zip(adults,new) for a,b in zip(row,nrow))
            if generation in {1,2,4,5,10,20,50,100,200,500,1000,horizon}:
                checkpoints.append({'generation':generation,'B_average':str(B),'RI':str(RI),'deme_gap':str(abs(q[0]-q[1])),
                  'background':list(map(str,background(new))),'maximum_adult_change':str(maximum_change),
                  'RI_change':None if old_ri is None else str(abs(RI-old_ri))})
            adults=new;old_ri=RI
        return {'model':'pure_induction' if pure_induction else 'genetic','precision':precision,'horizon':horizon,'checkpoints':checkpoints}

def exact_prefix_certificate():
    Q=Fraction
    adults=[[Q(0)]*10 for _ in range(2)]
    adults[0][INDEX[(2,2)]]=Q(1)
    adults[1][INDEX[(0,0)]]=Q(1)
    for n in range(1,5):
        adults=one_generation(adults,False,n==1,Q)
    conditional=[]
    for row in adults:
        gam=[Q(0)]*4
        for f,(a,b) in zip(row,GENOTYPES):
            gam[a]+=f/2
            gam[b]+=f/2
        conditional.extend([gam[1]/(gam[0]+gam[1]),gam[3]/(gam[2]+gam[3])])
    maximum=max(conditional)
    assert maximum<Q(1,14)
    return {'generation':4,'class_order':['deme1_e','deme1_E','deme2_e','deme2_E'],
       'conditional_B':[str(q) for q in conditional],'maximum_B':str(maximum),
       'genetic_RI_lower_given_written_invariant':str(1-8*maximum),
       'genetic_RI_gap_above_3_over_7':str(1-8*maximum-Q(3,7))}

def reduced_step(p, theta):
    """Genetic HW reduction, theta order d1e,d1E,d2e,d2E."""
    rows=[
       [3*(1-p)*(4-p),9*p*(1-p),p*(3+p),3*p*(1-p)],
       [9*p*(1-p),3*p*(3+5*p),3*p*(1-p),(1-p)*(8-5*p)]]
    rows.extend([list(reversed(rows[1])),list(reversed(rows[0]))])
    new_theta=[sum(w*q for w,q in zip(row,theta))/sum(row) for row in rows]
    return (2+2*p+2*p*p)/(5+2*p),new_theta


def exact_reduction_crosscheck():
    Q=Fraction
    adults=[[Q(0)]*10 for _ in range(2)]
    adults[0][INDEX[(2,2)]]=Q(1)
    adults[1][INDEX[(0,0)]]=Q(1)
    p=Q(6,7); theta=[Q(0),Q(0),Q(0),Q(1)]
    for n in range(1,5):
        adults=one_generation(adults,False,n==1,Q)
        marginals=[]
        for row in adults:
            g=[Q(0)]*4
            for mass,(a,b) in zip(row,GENOTYPES):
                g[a]+=mass/2;g[b]+=mass/2
            marginals.append(g)
        actual_theta=[q for g in marginals for q in (g[1]/(g[0]+g[1]),g[3]/(g[2]+g[3]))]
        assert actual_theta==theta, (n, actual_theta, theta)
        assert marginals[0][2]+marginals[0][3]==p
        assert marginals[1][2]+marginals[1][3]==1-p
        if n<4: p,theta=reduced_step(p,theta)
    return {'generations_checked':[1,2,3,4],'arithmetic':'exact Fraction',
       'genetic_background_generation4':str(p),'theta_generation4':list(map(str,theta)),
       'full20_state_vs_reduced':'identical at all four checked generations'}


def main():
    runs=[trajectory(epi,precision,horizon) for precision,horizon in [(50,500),(90,1000)] for epi in [False,True]]
    root=Path(__file__).parent
    finite={name:json.loads((root/(name+'-exact.json')).read_text()) for name in ['genetic','epigenetic']}
    delta=Fraction(finite['epigenetic']['RI'])-Fraction(finite['genetic']['RI'])
    with localcontext() as ctx:
        ctx.prec=75
        deterministic_genetic=Decimal(runs[2]['checkpoints'][-1]['RI'])
        finite_genetic=Fraction(finite['genetic']['RI'])
        finite_genetic=Decimal(finite_genetic.numerator)/finite_genetic.denominator
        finite_delta=Decimal(delta.numerator)/delta.denominator
        infinite_delta=Decimal(3)/7-deterministic_genetic
        comparison={'finite_genetic_RI':str(finite_genetic),'finite_epigenetic_advantage':str(finite_delta),
          'deterministic_advantage_numerical':str(infinite_delta),
          'finite_minus_deterministic_advantage_numerical':str(finite_delta-infinite_delta)}
    compact_runs=[]
    for run in runs:
        compact_runs.append({k:v for k,v in run.items() if k!='checkpoints'} |
            {'final':run['checkpoints'][-1],
             'RI_checkpoints':{str(c['generation']):c['RI'] for c in run['checkpoints']}})
    result={'mode':'deterministic source recursion, numerical asymptotic values; exact prefix sign certificate with written invariant',
       'parameters':{'m':'1/4','s':'1/2','r':'1/2'},'finite_exact_advantage':str(delta),
       'comparison':comparison,'exact_prefix':exact_prefix_certificate(),
       'exact_reduction_check':exact_reduction_crosscheck(),'runs':compact_runs}
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()