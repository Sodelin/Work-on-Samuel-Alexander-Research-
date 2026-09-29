# Necessity is now Lean checked for the existing population model

25 September 2026. This supersedes the earlier statement in
`ORDINAL-CHARACTERIZATION.md` and `VERIFICATION.md` that natural-certificate
necessity had only a written proof. Those files record the initial result.

`ReachableRankNecessity.lean` proves the full natural-certificate equivalence
for **every** graph `E` satisfying the existing `BinaryNatPopulation E` and
every binary target `s`. It imports the cached existing module
`SamuelAlexanderResearch.LayeredUnavoidability`; its definitions use the
repository's `LabelledGraph`, `FinitePath`, and `Realizes` directly.

The main checked endpoint, line 164, is:

```lean
theorem avoids_iff_has_natural_certificate (E : LabelledGraph) (s : Nat → Bool)
    (population : BinaryNatPopulation E) :
    (¬ Realizes E s) ↔ ∃ r, NaturalCertificate E s r
```

Here `Reachable E s v k` means some actual finite matching path of length `k`
starts at phase zero and ends at `v`. `NaturalCertificate E s r` requires

```text
reachable (v,k) and E v w (s k)  ==>  r w (k+1) < r v k.
```

The total function `rank` assigns zero to unreachable states; this is just
a total-function representation of a rank whose domain is the reachable
states. It does not assert decrease on transitions from unreachable states.

## What the proof constructs

- `reachable_endpoints_bounded`, line 40: actual avoidance implies bounded
  endpoints for every continuation from a reachable phase state. If endpoints
  were unbounded, the existing finite-branching `infinite_path_from_good`
  would produce an infinite tail. The existing `FinitePath.prepend_infinite`
  attaches the reaching prefix and contradicts `¬ Realizes E s`.
- `reachable_lengths_bounded`, line 53: strictly increasing vertex numbers,
  obtained from the actual population axioms, turn endpoint boundedness into
  a bound on continuation length.
- `reachable_maximum_exists`, line 82, and `rank_isMaximum`, line 99: the rank
  is an **attained** maximum of actual continuation lengths. The bound is
  derived inside the theorem, not supplied as a premise.
- `rank_isCertificate`, line 108: prefixing an edge to a child's maximum
  continuation proves strict decrease along each reachable phase transition.
- `rank_is_least`, line 141: this rank is pointwise least on reachable states
  among all natural certificates. Every certificate bounds every continuation
  length, and the chosen rank is attained.
- `avoids_iff_has_natural_certificate`, line 164: the complete equivalence.
- `aperiodic_Ps_has_natural_certificate`, line 173: specializes the necessity
  theorem to the existing graph `BinaryAvoidance.Edge s` whenever `s` is not
  eventually periodic. Both its population validity and its avoidance come
  from the existing proved endpoints.

The proof uses classical choice to select maxima uniformly. It does not
provide an effective bound or executable rank evaluator from an arbitrary
black-box avoidance proof.

## Exact remaining formal gap

The natural certificate existence, attained-maximality, strict decrease,
pointwise leastness, and equivalence with actual avoidance are now checked
for the repository's binary natural-date population model.

The following parts of the broader written ordinal theorem are still not
formalized by this module:

1. The explicit ordinal-valued rank of the matching-history tree, including
   the calculation that the artificial root has ordinal rank exactly omega.
2. The transfinite pruning equality at omega and extinction at omega+1.
3. The Schmidt-rank claim and the kernel calculation.
4. A formal adapter from an arbitrary finite alphabet and arbitrary real
   birthdates in the source paper to the binary natural-date model used here.

This module must therefore be described as a complete natural-certificate
characterization for the actual existing model, not as a formal proof of
the entire ordinal characterization in the source paper's full generality.

## Verification receipt

Command, using only the installed executable and cached imports:

```powershell
$env:LEAN_PATH = 'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization\.lake\build\lib\lean'
& 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe' 'C:\Users\Owner\Documents\Codex\2026-09-24\files-mentioned-by-the-user-1212\work\open-problems\ordinal\ReachableRankNecessity.lean'
```

Result: **exit code 0**, 3.772 seconds reported by the command runner.

All six printed endpoints depend on exactly:

```text
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` appears. The checked file contains no `sorry`, no `axiom`
declaration, and no admitted compactness or continuation-bound premise.

SHA-256 of `ReachableRankNecessity.lean`:

```text
DA2BE4D009966196E4B160789E968677B913385E2F7D4F037ED50281FED7FA50
```

The owning checkout was read only. No dependency download, cache fetch,
Lake build, publication, or archive mutation was performed for this proof.

### Exact compiler identity and endpoint reports

Direct compiler version:

```text
Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)
```

Exact printed endpoint names and axiom reports:

```text
'ReachableRankNecessity.reachable_endpoints_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.reachable_maximum_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.rank_isCertificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.rank_is_least' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.avoids_iff_has_natural_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
'ReachableRankNecessity.aperiodic_Ps_has_natural_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
```