# Stable formalization handoff

Observed 2026-09-30T00:01:02.779070+00:00. The proof sources are stable. Only the independent checkpoint rebuild is still producing output. No GitHub or website publication was performed by this handoff.

## Files to capture

Working source root: `C:\Users\Owner\Documents\Alexander-Open-Questions-2026-09-29\field-priorities\nanuq\formal-full`.

Frozen canonical checkpoint: `checkpoints/canonical-theta-20260929T233456Z`.
Its immutable `manifest.json` lists 94 Lean modules and exact source hashes. All 94 still match the working source. `src/CanonicalTheta.lean` is the local theorem entry point; `src/VerifiedCheckpoint.lean` collects the audited dependencies.

`PUBLICATION-HANDOFF-MANIFEST.json` records all 117 current Lean sources, local imports, source/log hashes, exclusions, and a topological build order for the 114 previously compiled modules. Cached objects and old logs are historical evidence, not a replacement for the fresh rebuild.

Capture `.lean`, `.md`, `.json`, `.py`, `.ps1`, relevant compiler `.log` files, and checkpoint source/context/manifests. Exclude `.olean`, `.ilean`, `.lake`, caches, and incomplete checkpoint directories. Keep failed/probe files in a clearly marked draft area or omit them from the verified build. Preserve dated manifests rather than overwriting them with newer claims.

## Completed formal endpoints

- `Nanuq.Canonical.theta_source`: arbitrary canonical theta arm counts (total at least one), original NANUQ circularity, pseudometric laws, strict separation, and exact support in the actual displayed edge splits.
- `Nanuq.Canonical.theta_weighted`: circularity, pseudometric laws, and exact displayed support for strictly positive rational terminal masses.
- `Nanuq.Canonical.theta_exact_quartet_mean`: the tensor is exactly the uniform mean over distinct displayed quartet resolutions. It is not a mean weighted by switching multiplicity.
- `RawNanuq`, `SourceFacts`, `SourceBlobFacts`: actual edge-indexed rooted binary DAG foundations, preserving parallel edges; switching trees, genuine displayed quartet resolutions, raw tensor symmetry/nonnegativity, source normalization, actual blob tree and port fibers. See each source for exact hypotheses.
- `GraphQuartetBridge`: a quartet with two branching blobs has a genuine original 2+2 bridge that forces its raw resolution.
- `GraphSwitchingChoices`: actual switching equivalence with hybrid incoming-edge choices, arbitrary subset extension, and subset/complement product equivalence.
- `Nanuq.AllLevelParameters.all_rows_iff_exact_domain`: the sixteen stated real inequalities are equivalent to `s=o=1`, `1/2 <= a <= 1`, `0 <= c <= a`. The same module proves the four-taxon inequality set is insufficient. This certifies the real algebra, not the external enumeration completeness.

Endpoint axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The finite theta certificates use kernel reduction. No new axiom, `sorry`, or native evaluation certificate is used for the completed endpoints.

## Additions outside the frozen dependency closure

`AllLevelParameterDomain`, `AnchorAdjacency`, `AnchorPortPatterns`, `AnchorPortCounts`, `AnchorPortFibers`, `AnchorPortValues`, `CircularComposition`, `GraphPortConsequences`, `GraphBlobMedian`, `GraphPortTransport`, `GraphMedianUnique`, `GraphPortFibers`, `GraphQuartetBridge`, `GraphSwitchingChoices`, `SourceBlobFacts`, `ThetaDeletedHybrid`, `ThetaFiniteEndpoint`, `TreePathCounting`, `TwoSwitchings`, `WeightedSmallPorts`.

These are separately compiled sources. Their dependencies and contemporaneous logs are in the manifest. They have not yet received one fresh combined rebuild with the frozen closure.

Excluded from the checked build: `GraphQuartetPortCounts` (known failed draft), `SourceProbe`, and `ThetaProbe` (scratch probes). `PORT-HELPERS-FROZEN.md` documents the failed wrapper. Its successful generic helper dependencies remain useful and are included.

## Exact remaining formal boundary

The complete raw-source all-level network theorem is NOT Lean checked. `AnchorComposition` proves aggregation conditional on the actual graph anchor identity. `CircularComposition` additionally needs local circularity and circular port preimages. The source graph representation/planarity and distinct-quartet preservation must still discharge those graph hypotheses. The canonical theta theorem alone does not prove classification of every raw blob.

The all-level computer-assisted argument, its representation and composition audits, and the new support audits belong to the adjacent research packet. This handoff does not independently recertify its recently reported support strengthening. Earlier dated scope notes remain historical and may predate that work.

The six-total-taxon structural bound remains established; minimality at six is not established. Five taxa already produce all sixteen inequality types in the external enumeration. The actual five-label witness in `FOUR-TAXON-OBSTRUCTION.json` rules out four total taxa for the full parameter-family criterion, not for every possible proof of original NANUQ. For positive cherry score `c`, the original multi-blob composition identity needs a correction; do not promote the local parameter theorem to a global family theorem unchanged.

## Fresh rebuild status

Observation: `{"status": "IN_PROGRESS", "completed_modules_observed": 22, "expected_modules": 94, "next_module": "ThetaCertificate6", "note": "File observations plus live runner status; full PASS requires the final receipt."}`.

The runner compiles all 94 frozen local sources into a new object directory, without importing the working directory's objects. It reuses the pinned external Mathlib/dependency libraries. Only a final `build-receipt.json` with `status: PASS` and 94 checked modules certifies completion. The receipt was not present at this observation.

## Reproduction

Pinned compiler: `Lean (version 4.33.1, x86_64-w64-windows-gnu, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release)`.
Pinned Mathlib commit: `0df444a360eaa60ab8c11dca51a86af692955474`.

On the original Windows host, run from the frozen checkpoint:

```powershell
python rebuild.py --build .
```

The original-host script checks snapshot hashes, the compiler binary hash, the Mathlib commit, exit codes, and printed axiom dependencies. Its compiler/package locations come from the frozen manifest and are absolute. It is not advertised as a path-independent project.

For another host, preserve the frozen snapshot unchanged. Install the pinned Lean version, check out the pinned Mathlib revision with its locked dependencies, and build or fetch that version's dependency libraries. Use `rebuild_publication.py` from this directory with explicit locations; it validates source hashes, the Lean version/commit and Mathlib revision, and creates a fresh output directory. It records the actual host compiler hash instead of requiring the original Windows executable's hash.

```text
python rebuild_publication.py --source-dir FORMAL_FULL --lean LEAN_EXECUTABLE --packages MATHLIB_PROJECT/.lake/packages --mathlib MATHLIB_PROJECT --scope checkpoint --output NEW_BUILD_DIRECTORY
```

The `--packages` directory must contain the dependency package directories; `--mathlib` separately points to the pinned Mathlib checkout. `--scope all-checked` includes the separately compiled additions in dependency order and excludes the three draft/probe modules. A successful run writes `build-receipt.json`; this helper has not been claimed to have completed a fresh all-checked build during this handoff.

The Python five-label witness reproducer imports `all_level_screen.py` and `independent_all_level_check.py`, and reads `parameter-domain.json` and `independent-all-level-check.json` from the adjacent research packet. Copy those together and adjust its single `root` path to that packet on the reproduction host. It uses Python standard-library exact fractions.
