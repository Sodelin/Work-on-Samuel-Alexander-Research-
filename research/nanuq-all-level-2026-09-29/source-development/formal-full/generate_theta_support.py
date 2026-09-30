from pathlib import Path
from itertools import product
root=Path(__file__).parent
counts=[t for t in product(range(7),repeat=4) if 1<=sum(t)<=6]
def term(t): return '⟨'+','.join(map(str,t))+'⟩'
def name(t): return 'support_checked_'+'_'.join(map(str,t))
for total in range(1,7):
    batch=[t for t in counts if sum(t)==total]
    lines=['import ThetaSupport','','set_option maxRecDepth 32768','set_option maxHeartbeats 0',
           '','namespace Nanuq.Theta','','/- Generated proof obligations only; no stored split or positivity answers. -/']
    for number,t in enumerate(batch,1):
        lines += [f'theorem {name(t)} : checkSupport {term(t)} = true := by decide +kernel']
        if number%10==0 or number==len(batch): lines += [f'#check {name(t)}']
    lines += ['',f'#print axioms {name(batch[-1])}','end Nanuq.Theta','']
    (root/f'ThetaSupportCertificate{total}.lean').write_text('\n'.join(lines),encoding='utf-8')
lines=['import ThetaCertificate',*(f'import ThetaSupportCertificate{k}' for k in range(1,7)),
       '', 'set_option maxRecDepth 32768', 'set_option maxHeartbeats 0', '', 'namespace Nanuq.Theta', '',
       'theorem all_support_checked : templates.all checkSupport = true := by',
       '  rw [templates_eq_explicit]', '  simp only [List.all_cons, List.all_nil, Bool.and_true,']
lines += ['    '+name(t)+(',' if i+1<len(counts) else ']') for i,t in enumerate(counts)]
lines += ['', '''/-- Every circular split is displayed by a concrete switching edge exactly
when one of its anchor coefficients is positive. The bounded nonnegativity
certificate combines this with positive-mass support invariance. -/
theorem bounded_support_exact (t : Counts)
    (hlo : 1 ≤ t.total) (hhi : t.total ≤ 6)
    {i j : Nat} (hij : i < j) (hj : j < (circular t).length) :
    displayedSplit t i j = true ↔
      ∃ p q, p < q ∧ q < (circular t).length ∧ 0 < alpha t p q i j := by
  have ht : checkSupport t = true :=
    List.all_eq_true.mp all_support_checked t (mem_templates_of_bounds t hlo hhi)
  exact support_iff_of_check ht hij hj

#print axioms all_support_checked
#print axioms bounded_support_exact
end Nanuq.Theta
''']
(root/'ThetaSupportCertificate.lean').write_text('\n'.join(lines),encoding='utf-8')
print('Generated exact edge-support proof obligations for all 209 templates.')
