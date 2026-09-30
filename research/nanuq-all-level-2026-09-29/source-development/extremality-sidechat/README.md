# NANUQ theorem audit package

This isolated side-conversation package contains a systematic theorem-extremality register, written proof refinements, and an exact executable finite verifier. It does not modify the main research checkout.

Start with [THEOREM-EXTREMALITY-REGISTER.md](THEOREM-EXTREMALITY-REGISTER.md): 96 stable audit IDs and 25 planned Lean proof contracts, with evidence levels and explicit stopping criteria. The same records are available in [extremality-register.json](extremality-register.json).

Read [PROOF-REFINEMENTS.md](PROOF-REFINEMENTS.md) for:
- analytic no-loss support, arbitrary-level support transfer, and multi-blob composition dependencies;
- sharp positive-weight and singleton bounds, optimal universal pendant baseline, and minimum support cardinality;
- the sharp strict raw-noise radius 1/2, with a four-taxon tree/cycle midpoint witness;
- the distinction between a five-label symbolic-catalogue minimum and the still-open five-label structural reduction;
- an explicit binary galled LSA level-2 counterexample outside the outer-labeled planar class.

Run the standalone verifier:

```text
node verify_nanuq.js
```

Compare its JSON output with [verification-results.json](verification-results.json). The saved program enumerates 84,076 tree configurations and 2,525,210 complete occurrence selections, and checks 24,667 anchor/split coefficients across 122 quartet systems. It also checks the symbolic rows and concrete endpoint witnesses. It uses no external dependencies, filesystem writes, network, or random sampling.

Execution provenance: the exact saved JavaScript source was executed in this conversation's JavaScript runtime and passed. A separate Node shell execution was unavailable because the shell sandbox helper could not initialize. The standalone entry point uses only standard JavaScript and console.log. This is not a Lean kernel receipt.

Unbounded graph statements require the written structural and composition proofs accepted in the main research thread; a successful finite execution does not replace them. Newly sharpened corollaries should receive independent review before publication.

No source repository commits, branch changes, external submissions, or archives were performed by this side package. The main chat owns publication integration.
