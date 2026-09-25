# Reproducing this checkpoint

Use [DEPENDENCIES.json](DEPENDENCIES.json) and [lake-manifest.json](lake-manifest.json) for exact dependency revisions. The Lean toolchain is leanprover/lean4:v4.33.1. All 13 custom source modules are included; .olean files are excluded.

## Integrity without compilation

Run:

```text
python verify_packet.py
```

Or, in PowerShell 7:

```powershell
pwsh -File ./Check.ps1
```

This checks manifest hashes, source/receipt correspondence, every saved selected axiom report, all relative Markdown links and the custom import closure. It neither downloads dependencies nor invokes Lean.

## Fresh replay

The route below is supplied for independent verification. It was not executed during packaging.

Use the pinned Elan toolchain. From this packet directory, Lake can retrieve the pinned dependency closure and the needed cached imports:

```text
lake exe cache get Mathlib.Probability.Independence.InfinitePi Mathlib.Probability.Distributions.Uniform Mathlib.Tactic.FinCases Mathlib.Tactic.Linarith Mathlib.Tactic.NormNum Mathlib.Tactic.Ring Mathlib.Tactic.FieldSimp Mathlib.Tactic.Positivity
```

Then:

```powershell
pwsh -File ./Check.ps1 -Run
```

The wrapper checks all nine Git revisions, compiles the 13 custom modules sequentially with -j1 -M4096, checks the printed axiom lists, and writes each replay to a new .replay directory. It preserves original logs, receipts and source files.

To reuse an already established pinned package directory rather than downloading again:

```powershell
pwsh -File ./Check.ps1 -Run -MathlibPackages 'C:/path/to/pinned/.lake/packages' -Lean 'C:/path/to/lean.exe'
```

The replay uses only fresh custom objects in its own output directory plus the chosen pinned package libraries. It does not silently use the original custom build objects.

## Recorded local checks

[COMBINED-RECEIPT.json](COMBINED-RECEIPT.json) records the four new module checks and their source/object/log hashes. The individual successful logs are preserved byte for byte under verification. The R1/R2 log is UTF-16; the verifier detects that encoding.

The original local wrappers and individual R3–R6 receipts are retained under provenance. [Cache acquisition](provenance/cache-acquisition.json) records the two successful targeted cache invocations, their exact local package root and output-object hashes. That metadata summarizes observed tool results, not a verbatim cache log.

Existing checked custom dependency objects were reused during development. All dependency sources are included for a fresh replay. Original object hashes are historical evidence: objects produced in a different directory need not have identical bytes. Reproducibility requires the same sources, successful checking and acceptable axiom reports.

The compilation slot was released before packaging. Integrity checks and packaging did not start another Lean or Lake process. No hosted CI result for this new packet is claimed by the local receipt.
