# Finite phase path theorem: local verification receipt

Date: 25 September 2026. This records a new local contribution for the next
research integration. It does not update the completed PR 5 release receipt.

## Verified file

- Repository path: `lean/SamuelAlexanderResearch/FinitePhasePaths.lean`.
- Exact local bytes SHA-256: `1d44c3afeb9158f4f7bd8a128f75b033aae77a3c7a438ed63ca28ed669d16aaf`.
- Compiler: Lean 4.33.1, matching `lean-toolchain`.
- Import: `Std` only.
- Direct compilation: passed, generating the module's object file.
- Endpoint axiom output: `propext`, `Classical.choice`, `Quot.sound` only.
- No `sorry` or new axiom declarations.

The endpoint `FinitePhasePaths.realizes_all` says that every infinite word
over an arbitrary label type is realized in a finite, nonempty phase graph
when every phase has an incoming edge of every label. The starting phase
may depend on the word. Its finite-branching argument is proved internally.

An independent read-only audit checked label order, the finite uniform bounds,
the choice recurrence and the exact conclusion. No substantive issue was
identified. This audit did not rerun compilation and is additional semantic
review, not a second compiler receipt.

Application to actual population paths requires the separately developed
port encoding, periodic quotient and lift. This receipt does not assert that
those additional files have passed. The helper and its explanatory note were
sent to the implementation owner; publication and aggregate CI belong to the
next integration.

## Formatting follow-up

A new `checks/check_math_format.py` validates protected GitHub inline math,
fenced displays and table pipes while excluding executable code. It found two
remaining indented display blocks in
`notes/FINITE-EDIT-STABILITY-FORMALIZATION.md`; their delimiters were changed
to math fences, with formula bodies preserved exactly.

After adding the helper's explanation, the local repository check covers
63 Markdown files, 2,073 inline formulas and 99 display formulas, with zero
formatting errors. The five new output proof/source notes separately pass
with 309 inline and 14 display formulas. This delimiter check does not replace
a TeX renderer or visual inspection on GitHub.

The completed public release remains documented in
[FINAL-RELEASE-RECEIPT.md](FINAL-RELEASE-RECEIPT.md). These new changes were
prepared locally and sent for integration, rather than silently modifying
that release's verification record.
