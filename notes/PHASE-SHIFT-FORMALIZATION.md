# Phase shifts of the binary avoiding graph

[`PhaseShift.lean`](../lean/SamuelAlexanderResearch/PhaseShift.lean) works with the actual labelled graph `BinaryAvoidance.Edge`, including its destination requirement $`2 \le w`$. A phase shift means `shift s a k = s (k + a)`, and a finite match means the existing `QuantitativeAvoidance.MatchesPrefix` predicate: every edge at time $`k`$ carries the target label at time $`k`$.

The construction and its sharp unshifted Thue–Morse endpoint are imported from the existing formalization. This module supplies the phase-shift transport argument. It reuses `FiniteEditStability`'s finite offset bound, displacement bound, backward-prefix construction, and path-splicing theorem rather than reproving them.

## Exact transport statements

`row_shift` proves, for every binary word $`s`$ and all natural $`a,w`$,

```math
\operatorname{row}(\operatorname{shift}(s,a),w)=\operatorname{row}(s,w+2a).
```
Consequently `edge_translate` carries each actual shifted edge to an original edge by adding $`2\cdot a`$ to both vertices. The reverse equivalence `edge_translate_iff` explicitly requires the shifted destination to be at least 2. `edge_subtract` requires original source at least $`2\cdot a`$ and original destination at least $`2\cdot a + 2`$. These conditions preserve the missing edge $`0 \to 1`$ and the behavior of natural subtraction.

`prepend_shifted_prefix` takes a length-$`\ell`$ match in $`P_{\operatorname{shift}(s,a)}`$ from vertex $`v`$ and constructs a length-$`\ell+a`$ match in $`P_{s}`$ from a vertex $`u`$ satisfying

```math
v\le u\le v+a.
```
The shifted path is first translated by $`2\cdot a`$. Its initial translated vertex is at least $`2\cdot a`$, so the shared backward construction can prepend the first $`a`$ labels of $`s`$. The theorem also records the exact suffix identity: the new path at time $`k+a`$ is the old path at time $`k`$ plus $`2\cdot a`$.

`suffix_subtraction` and `cut_original_prefix` prove the converse construction. A match in $`P_{s}`$ from $`u`$ with length $`\ell \ge a`$ yields a match in $`P_{\operatorname{shift}(s,a)}`$ of length $`\ell-a`$ from a vertex $`v`$ satisfying

```math
u-a\le v\le u,
```
where natural subtraction already truncates the lower bound at zero. The new path is explicitly `path (k+a) - 2*a`. The finite own-target lower bound $`2k\le\operatorname{path}(k)`$ ensures that every subtraction is valid and that every new edge destination is at least 2. The displacement bound gives the starting interval. No unrestricted graph-translation equivalence is assumed.

## Shifted Thue–Morse consequence

`thueMorse_shift_prefix_bound` uses the actual recursively defined `ThueMorseBits.t`. For every phase $`a`$, every start $`v \ge 1`$, and every matching prefix of length $`\ell`$ in the graph built from the shifted target, it proves

```math
3\ell\le8v+5a-1.
```
Indeed, the prepended original match has length $`\ell+a`$ and starts at some $`u \le v+a`$. The existing unshifted sharp theorem gives $`3\cdot (\ell+a) \le 8\cdot u-1`$, which implies the displayed bound. The nonnegative starting-bound convention is explicit: this endpoint assumes $`v \ge 1`$, just as the original sharp theorem does.

`thueMorse_shift_dyadic_family` proves the complementary existence family. For every $`q = 2^n`$ with $`a+2 \le 3\cdot q`$, it supplies an actual shifted matching path of length

```math
8q-a-3
```
from a positive vertex $`v`$ in the interval

```math
3q-a-1\le v\le3q-1.
```
The proof extracts an actual finite path from `SharpThueMorse.sharp_equality_family` through the shared `FiniteEditStability.sharp_family_prefix` theorem, then applies suffix subtraction. The original path starts at $`3\cdot q-1`$ and has length $`8\cdot q-3`$; neither its existence nor its equality-family formula is assumed as a new hypothesis. The side condition guarantees a positive shifted starting interval and sufficient length to cut $`a`$ edges.

The requested exact-equality claim at the left endpoint of a shifted dyadic starting interval remains outside the theorem. Phase-shift transport supplies bounded intervals for starts, and it does not by itself identify a shifted maximum or an exact equality location. Literal real-number coefficient statements belong to the separate optional Mathlib project.

## Validation

The complete module passed a direct Lean 4.33.1 check, and its compiled object was produced with:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/PhaseShift.lean
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean -o .lake/build/lib/lean/SamuelAlexanderResearch/PhaseShift.olean lean/SamuelAlexanderResearch/PhaseShift.lean
```

The module imports only the existing Std-based project. Its `#print axioms` declarations cover the translation, path-transport, shifted-bound, and dyadic-existence endpoints; they report only the standard axioms `propext`, `Classical.choice`, and `Quot.sound`, or a subset of them. There are no proof placeholders, custom axioms, or `native_decide` calls. No eventually-periodic positive theorem or larger-alphabet word classification is used by this phase-shift argument.
