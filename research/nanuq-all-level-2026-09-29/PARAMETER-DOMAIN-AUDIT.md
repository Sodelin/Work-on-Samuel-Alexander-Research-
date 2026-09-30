# Independent symbolic parameter-domain audit

**Verdict: pass.** Independent symbolic evaluation of the 122 previously verified adjacent-copy quartet systems reproduces exactly the 16 normalized nonzero rows in `parameter-domain.json`. Their simultaneous nonnegativity is exactly equivalent to

```math
s=o=1,\qquad \frac12\le a\le1,\qquad 0\le c\le a.
```

This is a two-dimensional domain for the stated **anchor-positivity criterion**, with the anchor-sharing entry fixed at 1. It is not a claim that parameters outside this domain necessarily fail circularity for an aggregated unweighted source-network distance.

## Independent computation

The input systems come from the prior exhaustive distance-based verifier's `independent-all-level-check.json`. No tree generation was repeated. Neither `parameter_domain.py` nor `all_level_screen.py` was imported or executed. The reference JSON was used to compare the derived rows and check its witness coefficients.

For each queried pair disjoint from its anchor pair, the independent evaluator classifies a singleton quartet directly as cherry or separated. For a two-topology quartet it instead uses adjacency in the four labels' cyclic order: successive positions are adjacent, positions two steps apart are opposite. Its symbolic entry is respectively `2c`, `2s`, `2a`, or `2o`. The exceptional entries involving anchors retain the specified 0 or 1. Thus the implementation does not reuse the target's count-of-separating-splits classifier.

It forms each four-term anchor coefficient as an exact integer vector in coordinates `(1,c,s,a,o)`, divides by the positive greatest common divisor of its entries, and collects the results. Positive division preserves the direction of the inequality.

| Labels | Saved systems | Symbolic coefficients | Identically zero | Distinct nonzero rows |
|---:|---:|---:|---:|---:|
| 3 | 1 | 9 | 6 | 1 |
| 4 | 3 | 108 | 36 | 10 |
| 5 | 16 | 1,600 | 550 | 16 |
| 6 | 102 | 22,950 | 9,339 | 16 |
| Total | 122 | 24,667 | 9,931 | 16 in the union |

The run took 0.204 seconds. The separate [symbolic receipt](independent-parameter-domain-check.json) records input hashes, occurrence counts, independent coefficient witnesses, exact algebraic certificates, and all four domain vertices.

All 16 reference witnesses were also checked: their packed quartet systems occur in the independently saved collection, and the stated anchors and boundary gaps yield the specified normalized row. This does not independently check the reference witness's duplication-mask field; no new tree enumeration was needed for the requested row comparison.

## The 16 rows and their simplification

Each expression in the middle column is required to be nonnegative. The final column substitutes `s=o=1`.

| Row in (1,c,s,a,o) | Inequality expression | After substitution |
|---|---|---|
| (-1,0,0,0,1) | o-1 | 0 |
| (-1,0,1,0,0) | s-1 | 0 |
| (0,-1,0,1,0) | a-c | a-c |
| (0,-1,1,0,0) | s-c | 1-c |
| (0,0,-1,0,1) | o-s | 0 |
| (0,0,-1,2,0) | 2a-s | 2a-1 |
| (0,0,0,1,0) | a | a |
| (0,0,1,-1,0) | s-a | 1-a |
| (0,0,1,0,-1) | s-o | 0 |
| (0,0,1,0,0) | s | 1 |
| (0,1,0,0,0) | c | c |
| (1,-1,0,0,0) | 1-c | 1-c |
| (1,0,-1,0,0) | 1-s | 0 |
| (1,0,0,-1,0) | 1-a | 1-a |
| (1,0,0,0,-1) | 1-o | 0 |
| (1,0,0,0,0) | 1 | 1 |

**Necessity for this criterion.** The rows `s-1` and `1-s` force `s=1`; `o-1` and `1-o` force `o=1`. The row `2a-s` then forces `a>=1/2`, and `1-a` forces `a<=1`. Finally, `c` and `a-c` force `0<=c<=a`.

**Sufficiency for this criterion.** Under those constraints, the last table column is termwise nonnegative. For an exact algebraic certificate, every entry is a nonnegative integer combination of `c`, `a-c`, `2a-1`, `1-a`, and the constant `1`; for example, `1-c=(1-a)+(a-c)` and `a=c+(a-c)`. The receipt supplies and verifies such a combination for every row.

In fact, the equivalence holds over all real quadruples `(c,s,a,o)`: the rows themselves imply nonnegative scores. The separately imposed nonnegativity assumption is therefore redundant for this particular inequality system.

The four vertices, in coordinates `(c,s,a,o)`, are `(0,1,1/2,1)`, `(1/2,1,1/2,1)`, `(1,1,1,1)`, and `(0,1,1,1)`. The checker also confirms every row at every vertex using exact fractions. The algebraic proof above establishes the full domain, not merely these four tests.

## Scope and use

This audit establishes equivalence for all coefficients in the independently verified finite collection on 3 through 6 labels. Transfer to universal anchor positivity for larger adjacent-copy trees uses the separately assigned restriction/relabeling argument. Transfer onward to the externally defined source-network distances additionally uses the representation and distance-decomposition proofs. Those structural steps were not re-audited here.

The criterion requires each anchor coefficient separately to be nonnegative. A distance obtained by summing anchor contributions may remain circular even when an individual coefficient is negative. Therefore a violated row outside the domain is a witness against **universal anchor positivity**, not automatically a counterexample to every unweighted distance or a necessity theorem for the external source class. The fixed anchor-sharing value 1 is also part of the criterion; this is not a scale-free assertion about arbitrary distance normalizations.

No source proof, original script, Git state, or publication record was changed. Only this audit and its separate symbolic receipt were created.

## Exact checker used

The following code is the independently executed checker. It reads the saved systems, writes the separate receipt, and performs no tree enumeration.

```python
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from math import gcd
from pathlib import Path
import json
import time

started = time.monotonic()
folder = Path(r"C:\Users\Owner\Documents\Codex\2026-09-29\vibemathed-biology\adjacent-nanuq")
input_names = ("independent-all-level-check.json", "parameter-domain.json", "parameter_domain.py")
hashes = {name: sha256((folder / name).read_bytes()).hexdigest() for name in input_names}
saved = json.loads((folder / input_names[0]).read_text(encoding="utf-8"))
reference = json.loads((folder / input_names[1]).read_text(encoding="utf-8"))
assert saved["status"] == "PASS_EXHAUSTIVE_FINITE_REPRESENTATION_CHECK"
zero = (0, 0, 0, 0, 0)
one = (1, 0, 0, 0, 0)

def entry(x, y, anchors, codes):
    if x == y or frozenset((x, y)) == anchors:
        return zero
    if x in anchors or y in anchors:
        return one
    quartet = tuple(sorted((x, y, *anchors)))
    code = codes[quartet]
    assert code in (1, 4, 5)
    if code == 5:
        # In the four-cycle, successive labels are adjacent and labels two
        # steps apart are opposite. This does not count separating splits.
        ix = 4 if abs(quartet.index(x) - quartet.index(y)) == 2 else 3
    else:
        side = (quartet[0], quartet[1]) if code == 1 else (quartet[0], quartet[3])
        ix = 1 if ((x in side) == (y in side)) else 2
    result = [0] * 5
    result[ix] = 2
    return tuple(result)

def coefficient(n, system, p, q, i, j):
    codes = dict(zip(combinations(range(n), 4), system))
    anchors = frozenset((p, q))
    terms = (entry(i, j, anchors, codes),
             entry((i+1) % n, (j+1) % n, anchors, codes),
             entry(i, (j+1) % n, anchors, codes),
             entry((i+1) % n, j, anchors, codes))
    return tuple(t[0] + t[1] - t[2] - t[3] for t in zip(*terms))

def normalize(row):
    factor = gcd(*row)
    return tuple(x // factor for x in row) if factor else zero

histogram = Counter()
witnesses = {}
size_rows = []
systems_by_n = {}
for item in saved["rows"]:
    n = item["taxa"]
    systems_by_n[n] = {tuple(system) for system in item["quartet_systems"]}
    row_counts = Counter()
    for system in systems_by_n[n]:
        for p, q in combinations(range(n), 2):
            for i, j in combinations(range(n), 2):
                raw = coefficient(n, system, p, q, i, j)
                row = normalize(raw)
                row_counts[row] += 1
                histogram[row] += 1
                if row != zero and row not in witnesses:
                    witnesses[row] = {"taxa": n, "system": list(system),
                                      "anchors": [p, q], "gaps": [i, j], "raw": list(raw)}
    assert sum(row_counts.values()) == item["anchor_coefficients"]
    size_rows.append({"taxa": n, "systems": len(systems_by_n[n]),
                      "coefficients": sum(row_counts.values()),
                      "zero_coefficients": row_counts[zero],
                      "distinct_nonzero_rows": len(set(row_counts) - {zero})})

actual = set(histogram) - {zero}
expected = {tuple(item["row"]) for item in reference["inequalities"]}
assert actual == expected and len(actual) == 16, (sorted(actual - expected), sorted(expected - actual))
reference_witnesses_checked = 0
for item in reference["inequalities"]:
    witness = item["witness"]
    n = witness["taxa"]
    length = len(tuple(combinations(range(n), 4)))
    system = tuple((witness["pattern"] >> (3*k)) & 7 for k in range(length))
    assert system in systems_by_n[n]
    raw = coefficient(n, system, *witness["anchors"], *witness["gaps"])
    assert normalize(raw) == tuple(item["row"])
    reference_witnesses_checked += 1

# Reduced coordinates are (constant, c, a), after substituting s=o=1.
# Generators are c, a-c, 2a-1, 1-a, 1.
generators = ((0,1,0), (0,-1,1), (-1,0,2), (1,0,-1), (1,0,0))
certificates = {
    (0,0,0): (0,0,0,0,0),
    (0,-1,1): (0,1,0,0,0),
    (1,-1,0): (0,1,0,1,0),
    (-1,0,2): (0,0,1,0,0),
    (0,0,1): (1,1,0,0,0),
    (1,0,-1): (0,0,0,1,0),
    (1,0,0): (0,0,0,0,1),
    (0,1,0): (1,0,0,0,0),
}
output_rows = []
for row in sorted(actual):
    reduced = (row[0] + row[2] + row[4], row[1], row[3])
    weights = certificates[reduced]
    assert min(weights) >= 0
    assert tuple(sum(weight * generator[i] for weight, generator in zip(weights, generators)) for i in range(3)) == reduced
    output_rows.append({"row": list(row), "occurrences": histogram[row],
                        "witness": witnesses[row], "after_s_o_equal_1": list(reduced),
                        "nonnegative_generator_weights": list(weights)})

necessary = ((-1,0,1,0,0), (1,0,-1,0,0),
             (-1,0,0,0,1), (1,0,0,0,-1),
             (0,1,0,0,0), (0,-1,0,1,0),
             (0,0,-1,2,0), (1,0,0,-1,0))
assert set(necessary).issubset(actual)
vertices = ((Fraction(0),Fraction(1),Fraction(1,2),Fraction(1)),
            (Fraction(1,2),Fraction(1),Fraction(1,2),Fraction(1)),
            (Fraction(1),Fraction(1),Fraction(1),Fraction(1)),
            (Fraction(0),Fraction(1),Fraction(1),Fraction(1)))
for vertex in vertices:
    assert all(sum(x*y for x,y in zip(row, (Fraction(1), *vertex))) >= 0 for row in actual)

report = {
    "status": "PASS_INDEPENDENT_SYMBOLIC_ROWS_AND_COMPACT_DOMAIN",
    "scope": "Universal nonnegative anchor coefficients over the independently saved adjacent-copy systems on 3..6 labels; no necessity assertion for aggregated unweighted source distances.",
    "input_sha256": hashes,
    "method": "Direct score classification from saved quartet systems, exact integer symbolic coefficients, positive-gcd normalization; no target imports and no tree enumeration.",
    "variables": ["constant_1", "c", "s", "a", "o"],
    "rows_by_size": size_rows,
    "total_systems": sum(len(systems) for systems in systems_by_n.values()),
    "total_coefficients": sum(histogram.values()),
    "identically_zero_coefficients": histogram[zero],
    "nonzero_normalized_rows": len(actual),
    "matches_reference_rows": actual == expected,
    "reference_witness_coefficients_checked": reference_witnesses_checked,
    "witness_scope": "Each referenced packed quartet system occurs in the independent system set, and its anchors/gaps yield the stated row. The source duplication-mask field was not separately checked.",
    "compact_domain": {"s": "1", "o": "1", "a": ["1/2", "1"], "c": ["0", "a"]},
    "nonnegative_scores_needed_as_extra_assumption": False,
    "necessity_row_subset": [list(row) for row in necessary],
    "sufficiency_generators_after_s_o_equal_1": ["c", "a-c", "2a-1", "1-a", "1"],
    "inequalities": output_rows,
    "vertices_c_s_a_o": [[str(x) for x in vertex] for vertex in vertices],
    "elapsed_seconds": round(time.monotonic() - started, 3),
}
output = folder / "independent-parameter-domain-check.json"
output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")
print(json.dumps({key: report[key] for key in ("status", "rows_by_size", "total_systems", "total_coefficients", "identically_zero_coefficients", "nonzero_normalized_rows", "matches_reference_rows", "elapsed_seconds")}, indent=2))
```

