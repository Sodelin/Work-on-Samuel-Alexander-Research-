# Reproduction and verification provenance

## Original successful check

The shared Sol2 worker ran Lean 4.33.1 in the existing pinned environment. Its receipt records compiler exit 0. The Alexander lead subsequently audited the final source, imported definitions, printed axioms and file hashes without running a second compiler.

The original PowerShell wrapper is preserved byte-for-byte in [provenance/Original-Check.ps1](provenance/Original-Check.ps1). With its default switches it performs a preflight; the successful compile used -Run. Its final invocation was:

```powershell
& 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe' -j1 -M4096 -o 'C:\Users\Owner\Documents\Codex\2026-09-25\feedback-speciation\pure-induction-ancestry\lean\build\PureInductionJoint.olean' 'C:\Users\Owner\Documents\Codex\2026-09-25\feedback-speciation\pure-induction-ancestry\lean\PureInductionJoint.lean'
```

The wrapper set LEAN_PATH to its isolated build directory, then the frozen finite-epigenetic build directory, then the pinned package library directories under the earlier alexander-formalization/real/.lake/packages checkout. It verified the four original frozen source and object hashes before the compile. Only FiniteFixation and FiniteEpigenetic are required local imports for this new checkpoint, so only their source files and earlier logs are bundled.

The [combined historical receipt](provenance/frozen-combined-receipt.json) also records two unrelated comparison modules; those modules are not part of this packet's replay. The [finite dependency receipt](verification/finite-dependency-receipt.json) covers the two bundled local dependencies.

## Pins and exact evidence

- Lean toolchain: leanprover/lean4:v4.33.1.
- Lean source commit: 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
- Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
- All nine Git package revisions are recorded in [DEPENDENCIES.json](DEPENDENCIES.json) and [lake-manifest.json](lake-manifest.json).
- New source SHA256: eaace6cf46a5e827c08fb7241d663e6c8e3290c5cabf58763cda7d1cbe99fd8a.
- Original object SHA256: 3516f055abea15f786e8f41918c0943e82f4f57bebc58df3b9b9841387c8f391.
- Original log SHA256: 81646e705e6f1bb0386b584c997a11c9127e6d1ed0cbc9691a681917718aaa8b.
- Worker receipt SHA256: 07325b3d81b928d74fc1981f71bf902a01501f6aa6d8f77483a2afffe5f002c1.
- Independent audit SHA256: 1cbe1feae4d27121977a3d300b29b93609a88e258ba13f1ab683a48a7ed5b81b.

Compiled .olean files are not shipped. The original object hash is historical verification evidence. A replay at a different filesystem location need not have the same object bytes; source identity, successful checking and printed axiom scope are the reproducibility target. The original log is UTF-16 with a byte-order mark; it has not been normalized.

## Integrity-only check

From the extracted packet directory, with Python 3:

```text
python verify_packet.py
```

This verifies all manifest members, saved selected axiom reports, source/receipt correspondence and relative Markdown links. It does not run Lean, download dependencies or change the original evidence.

PowerShell users can also run the portable wrapper without -Run:

```powershell
pwsh -File ./Check.ps1
```

## Fresh source replay

This route is supplied for the coordinator or another reviewer to execute. It was **not** executed during packaging, and no fresh-download success is claimed.

Install the pinned Lean toolchain using an existing Elan setup. From the packet directory, use Lake to obtain the dependencies/cache specified by the committed lockfile:

```text
lake exe cache get
```

Then run the portable wrapper in PowerShell 7:

```powershell
pwsh -File ./Check.ps1 -Run
```

The wrapper checks all package Git revisions, compiles FiniteFixation, FiniteEpigenetic and PureInductionJoint sequentially with -j1 -M4096, and writes new logs and objects to a unique .replay subdirectory. It preserves LEAN_PATH on return. It stops on compiler failure, source changes or unexpected axiom reports. The saved verification directory is never used for replay output.

The local path dependency named samuel_alexander_research was removed when deriving this standalone lockfile because none of these three source files imports it. The pinned Mathlib transitive Git revisions are unchanged. The Lake file follows the already-used three-library pattern; its fresh setup remains a reproduction obligation, not additional evidence for the mathematical claims.

## Publication disposition

Send this packet and its ZIP hash to the main coordinator, who owns publication and author correspondence. R1-R6 remain open as specified in [the scope audit](CHECKPOINT-AND-REMAINING-OBLIGATIONS.md). Do not label the four finite statements as the completed Alexander connection or as completed Wong formalization.
