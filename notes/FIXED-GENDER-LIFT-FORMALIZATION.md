# Fixed-gender lifts: the three-child productive core

`lean/SamuelAlexanderResearch/FixedGenderLift.lean` proves that every aperiodic Boolean word has an avoiding fixed-gender population with at most **three children per individual**. The whole retained population is weakly connected, specieslike, an inspecies, and satisfies REF. The module also verifies the earlier four-child construction obtained by deleting only two isolated root copies: it is specieslike but is not an inspecies.

These are universal Lean proofs, not conclusions drawn from finite scans. The underlying binary avoiding population and its fixed-source-gender lift come from the [classification manuscript, Sections 2–3](https://github.com/avg-netizen/biological-unavoidability/blob/main/paper.md). The earlier cleaned construction is stated in the supplied `notes/FIXED-GENDER-SPECIESLIKE.md`. Retaining only productive copies is the additional construction formalized here. No claim of literature priority is made. Alexander's definition of an inspecies is a minimal infinite ancestrally closed set; the formalization proves that minimality directly. See [Alexander, *Infinite graphs in systematic biology, with an application to the species problem*, Definition 4](https://arxiv.org/html/1201.2869).

## The actual population and its encoding

For a word `s : Nat → Bool`, write $`E_s(u,w,a)`$ for `BinaryAvoidance.Edge s u w a`. Its row labels satisfy

```math
r(2j)=s(j),\qquad r(2j+1)=\neg s(j).
```
For each $`w \ge 2`$, the incoming edges are $`(w-1) \to w`$ with label $`r(w)`$ and $`(w-2) \to w`$ with label $`\neg r(w)`$; there is no edge $`0 \to 1`$.

The lift encodes $`(v,b)`$ by `copy v b = 2*v + bit b`. It defines

```math
\operatorname{LiftEdge}_s(x,y)
\iff E_s\bigl(\operatorname{base}(x),\operatorname{base}(y),
                  \operatorname{gender}(x)\bigr),
```
where `base x = x / 2` and `gender x` is the parity bit. Thus every lifted edge is labelled by the **fixed gender of its source**. In pair notation, $`(u,a) \to (w,b)`$ holds exactly when $`E_s(u,w,a)`$, independently of $`b`$.

The two retained sets are:

| Formal predicate | Retained copies | Population bound and result |
| --- | --- | --- |
| `Core s x` | Exactly copies having at least one outgoing edge in the full lift | At most three children; the whole core is specieslike and an inspecies |
| `Clean s x` | All copies with base at least two, together with productive root copies | At most four children; the whole cleaned set is specieslike and is not an inspecies |

The graph induced by a retained set $`S`$ is explicitly `Induced E S x y := S x ∧ S y ∧ E x y`. Deleted natural-number codes are **not vertices of the population** and are not counted as extra roots. The strongest exported endpoint evaluates specieslike, inspecies, and REF in this induced graph.

`FixedGenderPopulation E S g cap` asserts the following concrete properties of the retained set:

1. $`S`$ is infinite.
2. Every edge between retained individuals strictly increases the encoded natural-number date.
3. Only finitely many retained individuals occur below each date.
4. The retained roots of the induced graph form a finite set.
5. Each retained individual has its retained children covered by a list of length at most `cap`.
6. Every retained nonroot has a retained parent of each Boolean gender, with an actual edge from that parent.

Finite parent sets also follow from strict dates: every parent of $`w`$ has code below $`w`$. The two distinct retained roots are proved exactly, rather than merely bounded:

```math
(0,\neg s(1)),\qquad (1,s(1)).
```
This is a genuine population on a retained subset of encoded naturals. It is not silently identified with `BinaryPopulation.BinaryNatPopulation`, whose vertex set is all naturals. No enumeration onto all naturals or transfer of the positive classification theorem through such an enumeration is exported by this module. Dates here are natural numbers; no real-date generalization is claimed.

## Why deleting all terminal copies gives three children

The core retains

```math
\operatorname{Core}_s(v,a)\iff\exists w\;E_s(v,w,a).
```
Every base index has a retained copy. At every odd index the retained gender is uniquely determined:

```math
\operatorname{Core}_s(2j+1,a)\iff a=s(j+1).
```
At base zero the retained gender is $`\neg s(1)`$. These identities handle the roots and the degree argument without exceptional unproved cases.

A source at base $`v`$ can have children only at bases $`v+1`$ and $`v+2`$. One of those bases is odd and has only one retained copy; the other has at most two. `core_child_cap_three` constructs the appropriate three-entry cover list for each parity of $`v`$. Removing the terminal copies preserves the required incoming edges: any parent of a retained child already has an outgoing edge, so that parent is productive and remains in the core.

The universal reachability bound is

```math
\operatorname{Core}_s(x)\ \land\
\operatorname{base}(x)+2\le\operatorname{base}(y)
\quad\Longrightarrow\quad
x\text{ is a strict ancestor of }y\text{ in the full lift}.
```
Indeed, a productive copy reaches both copies of one of its next two base indices. Once both copies at a positive base are reached, the source with the required row gender reaches both copies at the next base. Induction propagates this to every later base.

`core_induced_descendant_iff` proves that every path ending at a retained vertex survives restriction to the core. Every intermediate vertex has an outgoing edge along the path and is therefore retained. Consequently, each core individual is a strict ancestor of all but finitely many core individuals, with the explicit non-descendant bound

```math
\neg\operatorname{Descendant}(x,y)
\quad\Longrightarrow\quad y<2\bigl(\operatorname{base}(x)+2\bigr).
```
This yields IAP. Two core individuals have a common retained descendant sufficiently far ahead, giving weak connectivity. Convexity is proved both in the full lift and in the induced graph. For inspecies minimality, let $`T`$ be an infinite ancestrally closed subset of the core. If a core individual $`x`$ were absent from $`T`$, none of its strict descendants could lie in $`T`$. The displayed bound would make $`T`$ finite, a contradiction. Thus $`T`$ must equal the core. These structural conclusions require no aperiodicity hypothesis and no supplied compactness or cofinite-ancestry premise.

For avoidance, a fixed-gender path with `gender(path k) = s k` projects under `base` to a matching path in `BinaryAvoidance.Edge s`. The already proved `aperiodic_target_avoided` theorem rules this out when $`s`$ is not eventually periodic. The path begins at phase zero and reads the source gender of its kth edge.

## Exported endpoints

The main endpoint is `FixedGenderLift.productive_core_induced_avoider`. Its only word hypothesis is `¬ EventuallyPeriodic s`; it proves the conjunction

```lean
FixedGenderPopulation (LiftEdge s) (Core s) gender 3 ∧
Specieslike (Induced (LiftEdge s) (Core s)) (Core s) ∧
Inspecies (Induced (LiftEdge s) (Core s)) (Core s) ∧
Reflection (Induced (LiftEdge s) (Core s)) (Core s) ∧
¬ ∃ path : Nat → Nat, ∀ k,
  Induced (LiftEdge s) (Core s) (path k) (path (k + 1)) ∧
  gender (path k) = s k
```

`productive_core_avoider` also states the specieslike and inspecies conclusions for the core as a subset of the full lift. Other useful endpoints include:

- `core_reaches_late` and `core_nonDescendants_bounded`: explicit universal ancestry bounds.
- `core_child_cap_three`: the child bound, independent of aperiodicity.
- `core_roots_exactly` and `core_roots_distinct`: the exact two roots.
- `core_fixedGenderPopulation`: all population conditions for the retained core.
- `core_induced_descendant_iff`: the actual restriction bridge; this theorem depends on no axioms.
- `core_induced_specieslike`, `core_induced_inspecies`, and `core_induced_reflection`: the separate induced-graph structural theorems.

## The earlier four-child construction remains a distinct result

`Clean s` removes only $`(0,s(1))`$ and $`(1,\neg s(1))`$, the two isolated copies at root bases. It keeps both copies at every base at least two. `clean_roots_exactly` proves that its retained roots are the same two productive roots as above. `clean_avoider` proves the four-child population conditions, weakly connected specieslike status, aperiodic avoidance, and failure of inspecies minimality.

The explicit retained terminal family is

```math
\operatorname{TerminalCopy}_s(j)
  =\bigl(2j+3,\neg s(j+2)\bigr),\qquad j\ge0.
```
`terminal_copy_clean`, `terminal_copy_not_core`, and `terminal_copy_no_children` prove the membership and terminal claims; `terminal_copies_infinite` proves that this family is infinite. The core is an infinite ancestrally closed proper subset of the cleaned population, so `clean_not_inspecies` follows directly from the definition. This comparison preserves the original written claim rather than incorrectly upgrading the graph that still contains those terminal copies.

## Reproduction and remaining scope

From the repository root in PowerShell:

```powershell
$env:ELAN_HOME = 'C:\Users\Owner\.elan'
$env:PATH = 'C:\Users\Owner\.elan\bin;' + $env:PATH
& 'C:\Users\Owner\.elan\bin\lake.exe' env lean lean/SamuelAlexanderResearch/FixedGenderLift.lean
```

The module compiles with Lean 4.33.1 and the existing Std-only project. Its fourteen selected `#print axioms` endpoints pass. Each depends only on a subset of `propext`, `Classical.choice`, and `Quot.sound`; `core_induced_descendant_iff` has no axiom dependencies. There are no `sorry`, custom axioms, `native_decide` endpoints, or Mathlib additions. The final standalone compilation exits successfully without warnings.

The formal result supplies a three-child fixed-gender avoiding construction for every aperiodic Boolean target. It does not settle whether two children suffice, does not claim the three-child bound is optimal, and does not by itself export a full fixed-gender unavoidability classification over retained-subset populations. The latter positive direction needs an explicit model transfer or an extension of the positive theorem to this population interface. Literature priority and broader real-date population results remain separate questions.
