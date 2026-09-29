# Adaptive spatial-mark law

The source audit identified a gap between independent stored marks and the
conditional law of the mark selected by an evolving lineage frontier.
`real/WongAdaptiveSelection.lean` closes that gap. These are probability
lemmas supporting Appendix B, not new biological claims.

The first verified version passed the serialized checker in 26.501 seconds.
The six-module dependency closure uses the pinned Mathlib revision. The
preserved log and source/object-hash receipt are
`WongAdaptiveSelection-stage1.log` and `WongAdaptiveSelection-stage1.json`.
This is a working-tree module receipt, not the final combined exact-commit
receipt; the root integration lane owns that check.

For event index t, `pastSigma t` contains all innovation coordinates `(j,s)`
with j<t. Independence of this whole sigma-field from each current coordinate
is derived from infinite-product independence and disjoint index sets.
Countable disjoint selector fibres then give, for a past-measurable selector
S, past event A, and measurable mark event B:

```
P(A and M(t,S) in B) = sum_s P(A and S=s) * markLaw(s)(B).
```

This cylinder identity is proved, not assumed. The general theorem takes
fixed-coordinate independence as a hypothesis; the actual-array theorem
derives it from the constructed product law. All seven printed stage-one
endpoints use only `propext`, `Classical.choice`, and `Quot.sound`; none uses
`sorryAx` or `Lean.ofReduceBool`.

The product-space integration step passed in 27.290 seconds and is preserved
in `WongAdaptiveSelection-stage2.json` and its log. It fixes the entire
count-clock path and lifts the sectionwise identity by product integration.
This use of the whole
count-clock path is valid for the spatial-mark law because that whole path
is independent of the array. It does not imply a conditional exponential
waiting-time claim under a sigma-field revealing future clocks.

The concrete-recorder step passed in 26.326 seconds, with an 18-module
dependency closure. `measurable_recordPrefix_section` derives measurable
dependence of the actual `recordPrefix`, including failure branches, on
innovation rows before t after fixing the count-clock path. The proof uses
the recorder lane's verified coordinate-measurability theorem and natural
Borel state encoding.

`recorder_mark_cylinder` then proves the exact selected-mark cylinder identity
for every measurable H in the entire count-clock path and actual t-event
prefix. It does not assume adaptedness of the recorder or the cylinder
identity. All 14 final printed endpoints use only the standard three axioms.
The final source SHA256 is
`ac8ec96239575413b57d731742d126047d7d69725aa180b27a875d161fbb0163`;
the object SHA256 is
`e4fd7da691c45453e4278cace23d5046b0443af80a6ba86f9dde1e283b4effd2`.
`WongAdaptiveSelection-final.json` and `.log` preserve the exact module
receipt. The shared summary had already been replaced by the following
Dated check when copied; it is correctly named
`shared-dated-closure-receipt.json`, not an adaptive closure receipt.

This lane's proof source is frozen. Root still owns final registration,
integration, and the exact-commit combined replay, including any later
dependency changes. The independent source-family update is
`FINAL-COVERAGE-DELTA.md` and `final-coverage-delta.json`.
