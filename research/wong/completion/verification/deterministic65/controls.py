"""Finite independent sanity/false controls. These are not Lean proofs."""
from __future__ import annotations
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

STAGE = Path(__file__).resolve().parent

def reach(edges, a, b):
    seen, todo = set(), [v for u, v in edges if u == a]
    while todo:
        v = todo.pop()
        if v == b:
            return True
        if v not in seen:
            seen.add(v)
            todo.extend(t for s, t in edges if s == v)
    return False

def anc(edges, a, b):
    return a == b or reach(edges, a, b)

def supported(edges, samples):
    return {(p,c) for p,c in edges if any(anc(edges,c,s) for s in samples)}

def truncated(edges, samples):
    return {(p,c) for p,c in supported(edges,samples)
            if not all(anc(edges,c,s) for s in samples)}

def mrcas(nodes, edges, samples):
    common = {a for a in nodes if all(anc(edges,a,s) for s in samples)}
    return {m for m in common if all(anc(edges,a,m) for a in common)}

def merge(pieces):
    result = []
    for lo,hi in reversed(pieces):
        if result and hi == result[0][0]:
            result[0] = (lo,result[0][1])
        else:
            result.insert(0,(lo,hi))
    return result

def separated(pieces):
    return all(a[1] < b[0] for i,a in enumerate(pieces) for b in pieces[i+1:])

def covers(pieces,x):
    return any(lo <= x < hi for lo,hi in pieces)

def main():
    results=[]
    def check(name, observed, expected, meaning):
        assert observed == expected, name
        results.append(dict(name=name,observed=observed,expected=expected,meaning=meaning))
    nodes=set(range(6))
    edges={(0,1),(1,2),(2,3),(1,4)}
    samples={3,4}
    check('supported edge into MRCA is removed', (0,1) in supported(edges,samples) and
          (0,1) not in truncated(edges,samples), True,
          'Kills the false equality between support filtering and truncation.')
    check('unique MRCA of the worked graph', sorted(mrcas(nodes,edges,samples)), [1],
          'Finite independent instance of the explanatory diagram.')
    check('MRCA-to-sample paths survive', all(reach(truncated(edges,samples),1,s) for s in samples),
          True,'Survival is checked from the MRCA, not from older removed ancestors.')
    check('older-ancestor paths do not survive', reach(truncated(edges,samples),0,3), False,
          'Kills the false claim of all original ancestry preservation.')
    check('singleton sample leaves no edges', len(truncated(edges,{3})),0,
          'Reflexive sample ancestry makes the singleton already coalesced.')
    check('empty samples leave no edges',len(truncated(edges,set())),0,
          'Support filtering prevents vacuous common ancestry from retaining edges.')
    check('ancestral sample stays protected', (1,4) in truncated(edges,{1,4}),True,
          'The ancestral sample can have one child; an all-vertices arity claim is false.')
    diamond={(0,2),(0,3),(1,2),(1,3)}
    check('without unique parents MRCA existence can fail',sorted(mrcas(set(range(4)),diamond,{2,3})),[],
          'Two incomparable common ancestors defeat an unconditional existence claim.')
    check('sampled-root forest has no MRCA',sorted(mrcas({0,1},set(),{0,1})),[],
          'Common-ancestor existence is a real premise.')
    unsupported=edges|{(0,5)}
    check('sample traces miss an unsupported branch',supported(unsupported,samples)==unsupported,False,
          'Kills the unconditional Appendix E sample-array inverse.')
    pieces=[(0,1),(1,2),(2,3),(5,6)]
    check('touching pieces merge and real gap remains',merge(pieces),[(0,3),(5,6)],
          'Matches the separately kernel-checked Lean example.')
    check('gap-filling changes semantics',covers([(0,1),(2,3)],1)==covers([(0,3)],1),False,
          'Kills the false claim that arbitrary gaps may be filled.')
    check('overlap violates ordered-input separation claim',separated(merge([(0,2),(1,3)])),False,
          'The ordered nonoverlap premise cannot be removed.')
    check('unsorted input need not normalize',separated(merge([(2,3),(0,1)])),False,
          'The list merge is not a sorting algorithm.')
    check('empty interval is outside proper-interval type',0<0,False,
          'Zero-span annotations are not values of Interval; empty region sets are allowed separately.')
    report={'status':'PASS_FINITE_CONTROLS','checked_at_utc':datetime.now(timezone.utc).isoformat(),
            'count':len(results),'scope':'Independent finite Python sanity and deliberately false controls; not a Lean proof or whole-paper test.',
            'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),'controls':results}
    (STAGE/'evidence/finite-controls.json').write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: {len(results)} finite controls, including explicit rejected overgeneralizations.')

if __name__=='__main__':
    main()
