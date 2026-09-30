# Frozen port-helper status

The following modules compiled with Lean 4.33.1 and only standard axioms before the parent redirected work to the bounded four-taxon assessment:

- `AnchorPortPatterns.lean`: omitTriple via Fin.succAboveEmb, exact 4/2/0 injective-triple counts from occupied-port counts.
- `AnchorPortCounts.lean`: four unique triple medians force one four-port center or two three-port centers.
- `AnchorPortFibers.lean`: a bridge transport premise plus at least three occupied ports on both sides forces a two-taxon fiber.
- `AnchorPortValues.lean`: exact ordered-anchor value by port collision pattern; at most two ports contribute zero.

`GraphQuartetPortCounts.lean` is preserved but is NOT a successfully compiled module. Its unique_omitted_triple_port proof checked, but the summation/classification declaration statements require explicit classical Fintype and DecidableEq instances. Its log reports those failures and must not be treated as a proof receipt. No repair or expansion was started after the parent requested freezing this lane.