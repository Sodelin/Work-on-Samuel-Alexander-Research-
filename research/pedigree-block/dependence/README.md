Repeated-block dependence: proof checkpoint

Owned source: real/PedigreeBlockDependence.lean.
Imports: PedigreeBlockProbability and the frozen PedigreeBlockGraph.
There is no Recovery import and therefore no dependency cycle.

Draw x from the checked uniform one-block law configLaw n 1, on n+1 labeled
children. Define repeatBlock B x by giving child i the bit x i 0 at EVERY
block. The measure repeatedLaw n B is the actual pushforward of configLaw n 1
under this deterministic map.

For B>0, repeatBlock_share_iff proves equality of sharing edges before and
after repetition. The direction back to the one-block graph discards the
repeated block index. The forward direction uses an available block, supplied
by B>0. Consequently repeatBlock_connected_iff proves that the entire
connectedness event is unchanged.

readBlock b extracts block b as a one-block configuration on the same labeled
children. The identity readBlock b (repeatBlock B x) = x holds pointwise.
The measurable pushforward composition therefore yields:

    (repeatedLaw n B).map (readBlock b) = configLaw n 1.

This is equality of the whole joint law across children at each block. The
source law's checked config_bit_cylinder theorem supplies its fair,
independent-across-child interpretation. Correct individual-block laws do not
assert independence between distinct blocks.

The general probability endpoints are:

    repeatedLaw_connected_eq_one_block:
      repeatedLaw n B {x | Connected x}
        = configLaw n 1 {x | Connected x}

    repeatedLaw_connected_probability:
      repeatedLaw n B {x | Connected x}
        = 1 - ((2^n - 1 : Nat) : ENNReal) / (2 : ENNReal)^n

Both require B>0 and hold for every natural n, including the singleton case.
The final expression is independent of B. It is obtained from the measured
preimage of the actual connectedness event and the checked one-block
exceptional probability, rather than assigning an event mass by definition.
The optional algebraic simplification to 2^(-n) is not a separate Lean
endpoint in this module.

The selected printed endpoints are:

- PedigreeBlock.repeatBlock_share_iff
- PedigreeBlock.repeatBlock_connected_iff
- PedigreeBlock.repeatedLaw_probability
- PedigreeBlock.repeatedLaw_block_marginal
- PedigreeBlock.repeatedLaw_connected_eq_one_block
- PedigreeBlock.repeatedLaw_connected_probability

This is a general observation-law counterexample, not a two- or three-child
enumeration. It establishes no coupling to Wong's marked ARG, no monotonicity
in Wong's recombination-rate parameter, no multigeneration REC-GEN theorem,
and no Alexander specieslike classification. Additional independent-block
claims require their own probability assumptions.

Reproduce this lane through the coordinated compiler lock:

```powershell
$env:WONG_COMPILER_LOCK = 'C:\Users\Owner\Documents\Codex\2026-09-27\wong-alexander\.local-build\wong-continuation\compiler.lock'
python -X utf8 research\wong\continuation-2026-09-27\check.py PedigreeBlockDependence
```

The verifier uses pinned Lean 4.33.1 and mathlib
0df444a360eaa60ab8c11dca51a86af692955474. RESULT.json and the preserved module
log/row and import-closure receipt record development verification; they do
not replace the coordinating lane's final combined clean-commit audit.

Development verification passed at the first actual compilation of this module
(25.252 seconds, four project modules in the checked import closure). The
earlier verifier attempt stopped in a shared dependency before reaching this
source; that dependency's owner repaired and froze it. Its earlier diagnostic
is preserved as dependency-attempt-1. All six selected endpoints are checked
with only standard allowed axioms. RESULT.json pins this frozen source.
No source edits or additional proofs remain pending in this lane.
