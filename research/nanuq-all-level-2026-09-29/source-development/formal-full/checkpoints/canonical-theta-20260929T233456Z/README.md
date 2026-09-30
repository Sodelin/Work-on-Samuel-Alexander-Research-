# Checked canonical theta theorem

Entry point: `src/CanonicalTheta.lean`. Consolidated audit: `src/VerifiedCheckpoint.lean`. Read `context/OBLIGATIONS.md` for the boundary between the completed local theorem and the unfinished raw N2 graph theorem.

Rebuild with the pinned compiler and installed dependency cache:

```powershell
python rebuild.py --build .
```

The rebuild compiles every included local source in dependency order. It uses a new build directory and does not import working-directory object files. It does reuse the existing pinned Mathlib dependency libraries. Its result is `build-receipt.json`; the manifest itself is an immutable source snapshot. No native-decide certificate or external Boolean result certifies a Lean theorem.
