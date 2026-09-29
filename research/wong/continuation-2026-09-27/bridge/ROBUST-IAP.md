The IAP bridge tolerates finitely many wrong ancestry answers per representative.

Let q map rich-history nodes to organisms, let S be an organism candidate, and
let C = q⁻¹(S) include all rich representatives of its members. Assume q is onto
and every fibre q⁻¹({v}) is finite. For each a in C, assume the following
disagreement set is finite:

    Δ(a) = { b in C : (a is an R-ancestor of b)
                      differs from (q(a) is an E-ancestor of q(b)) }.

Then C has Alexander's identical-ancestor property (IAP) in R exactly when S
has IAP in E. The new Lean endpoint is
`WongPedigreeRobust.iap_iff_of_finite_projection_errors`, in
`real/WongPedigreeRobust.lean`. The stable bridge module is unchanged.

This strengthens the earlier bridge specifically for IAP. It permits
disagreements between different owners, a different finite error set for every
representative, and no common bound on their sizes. It requires no agreement
for ancestors outside C or descendants outside C. It does not assume ancestry
soundness, acyclicity, or connected fibres. Those absences are correct for this
predicate-level equivalence; a biological interpretation of q and either
graph remains a separate obligation.

**Proof.** Fix a in C. Its descendant set in C and the inverse image under q
of its owner's descendant set in S differ only on Δ(a). Removing or adding
finitely many members cannot change whether a set is finite. Their relative
complements in C also differ only on Δ(a), so their finiteness agrees as well.
An inverse image under an onto map with finite fibres is finite exactly when
the original set is finite. Therefore, for this representative, the rich
descendant set is finite exactly when its owner's pedigree descendant set is
finite; the same holds for the nondescendant sets. IAP is precisely the
alternative that one of these two sets is finite for every candidate member.
Surjectivity supplies a representative when transferring the universal
statement to an organism. In the reverse direction the same argument works
for every representative. The Lean proof mechanizes these steps.

The new condition includes the earlier exact-between-different-owners
condition: if ancestry agrees whenever the two owners differ, Δ(a) lies in
the finite fibre of q(a). It is strictly weaker. For a simple written example,
take q to be the identity, S to be all natural numbers, and consider the two
infinite chains

    E: 0 → 1 → 2 → 3 → 4 → ...
    R: 1 → 0 → 2 → 3 → 4 → ...

The ancestry answer from 0 to 1 differs, as does the answer from 1 to 0.
All other ancestry answers agree. Thus Δ(0)={1}, Δ(1)={0}, and the remaining
disagreement sets are empty, even though exact agreement between different
owners fails. This example illustrates strict weakening; it is a written
argument rather than a second Lean theorem in this bounded addition.

Finite error means finitely many disagreeing **ancestry-path answers**, not
finitely many edited immediate-parent edges. For example, deleting the first
edge of the chain 0→1→2→... changes infinitely many ancestry answers from 0.
The result also does not establish that errors from genome sampling or ARG
inference satisfy the finite-disagreement condition. The earlier owner-map
counterexample and finite-observation obstruction remain applicable.

**Source and prior-work boundary.** Alexander defines IAP by requiring each
member to have finitely many descendants or finitely many nondescendants
inside the candidate. The theorem here is a new mechanized deduction from
that definition and elementary finite-set facts; it is not attributed to the
paper, and no claim of mathematical novelty is made.
[Alexander, Definition 2](https://arxiv.org/html/2602.05274v1)

The already checked prior-work context is unchanged: Gravel and Steel study
genealogical ancestors that leave no inherited material under a specified
biparental recombination model, while Thatte studies distributional pedigree
identifiability under explicit recombination and mutation assumptions.
Neither source is being cited as establishing the finite-disagreement
hypothesis used here.
[Gravel and Steel, section 2 and Proposition 2.1](https://www.math.canterbury.ac.nz/~m.steel/Non_UC/files/research/ghosts.pdf),
[Thatte, Proposition 4.6, Theorem 5.13, and section 6](https://arxiv.org/pdf/1008.0153)

This theorem alone carries no convexity, connectivity, REF, maximality, or
specieslike conclusion. In particular, IAP transfer does not assign a
biological species classification.

**Verification.** The serialized command is:

```powershell
python -X utf8 research\wong\continuation-2026-09-27\check.py WongPedigreeRobust
```

The source prints the axiom dependencies of its single new endpoint.
Compilation and exact-commit status are recorded separately in
`verification/ROBUST-RESULT.json`; a source draft is not a successful receipt.


The source snapshot passed on its first compiler attempt: 35 project modules,
19.047 seconds for the new module, one printed acceptance endpoint, and only
the standard dependencies propext, Classical.choice, and Quot.sound. The
preserved result records the source hash; final combined exact-commit
verification remains separate.
