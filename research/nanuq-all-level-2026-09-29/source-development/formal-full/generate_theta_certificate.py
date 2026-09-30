from pathlib import Path
from itertools import product
root = Path(__file__).parent
counts = [t for t in product(range(7), repeat=4) if 1 <= sum(t) <= 6]
assert len(counts) == 209

def term(t):
    return '⟨' + ','.join(map(str,t)) + '⟩'

def name(t):
    return 'checked_' + '_'.join(map(str,t))

for total in range(1,7):
    batch = [t for t in counts if sum(t) == total]
    lines = ['import ThetaFiniteSoundness', '', 'set_option maxRecDepth 32768',
             'set_option maxHeartbeats 0', '', 'namespace Nanuq.Theta', '',
             '/- Each assertion is checked by kernel reduction of the executable',
             'switching/quartet evaluator. This generator supplies no metric answers. -/', '']
    for number, t in enumerate(batch,1):
        lines += [f'theorem {name(t)} : checkTemplate {term(t)} = true := by decide +kernel']
        if number % 10 == 0 or number == len(batch):
            lines += [f'#check {name(t)}']
    lines += ['', f'#print axioms {name(batch[-1])}', 'end Nanuq.Theta', '']
    (root / f'ThetaCertificate{total}.lean').write_text('\n'.join(lines),encoding='utf-8')

lines = [*(f'import ThetaCertificate{k}' for k in range(1,7)), '',
         'set_option maxRecDepth 32768', 'set_option maxHeartbeats 0', '',
         'namespace Nanuq.Theta', '',
         '/-- Exact coverage of the generated list, proved by kernel evaluation. -/',
         'theorem templates_eq_explicit : templates = [']
lines += [('  ' + term(t) + (',' if i+1<len(counts) else '')) for i,t in enumerate(counts)]
lines += ['] := by decide +kernel', '',
          '/-- Assembled complete certificate; no recomputation of the large table',
          'is needed after the individual kernel-checked template lemmas. -/',
          'theorem all_templates_checked : templates.all checkTemplate = true := by',
          '  rw [templates_eq_explicit]',
          '  simp only [List.all_cons, List.all_nil, Bool.and_true,']
lines += ['    ' + name(t) + (',' if i+1<len(counts) else ']') for i,t in enumerate(counts)]
lines += ['',
'''theorem bounded_anchor_nonnegative (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    {p q i j : Nat} (hpq : p < q) (hq : q < (circular t).length)
    (hij : i < j) (hj : j < (circular t).length) :
    0 ≤ alpha t p q i j := by
  have ht : checkTemplate t = true :=
    List.all_eq_true.mp all_templates_checked t (mem_templates_of_bounds t hlo hhi)
  exact template_anchor_nonneg ht hpq hq hij hj

theorem bounded_quartets_checked (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6) : checkQuartets t = true := by
  have ht : checkTemplate t = true :=
    List.all_eq_true.mp all_templates_checked t (mem_templates_of_bounds t hlo hhi)
  have hparts : checkQuartets t = true ∧ checkAnchors t = true := by
    simpa [checkTemplate] using ht
  exact hparts.1

theorem exact_coefficient_count :
    (templates.map fun t => (pairs (circular t).length).length ^ 2).sum = 100823 := by
  decide +kernel

#print axioms all_templates_checked
#print axioms bounded_anchor_nonnegative
#print axioms bounded_quartets_checked
#print axioms exact_coefficient_count
end Nanuq.Theta
''']
(root / 'ThetaCertificate.lean').write_text('\n'.join(lines),encoding='utf-8')
print('Generated 209 kernel proof obligations, six bounded batches, and coverage assembly.')
