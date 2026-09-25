# Ordinal-lane verification receipt

Date: 25 September 2026.

The direct installed executable was used, with no Lake build or dependency
fetch:

```powershell
& 'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe' 'C:\Users\Owner\Documents\Codex\2026-09-24\files-mentioned-by-the-user-1212\work\open-problems\ordinal\OrdinalCertificates.lean'
```

Result: exit code 0, 3.096 seconds reported by command execution.

```text
'OrdinalCertificates.certificate_bounds_every_prefix' depends on axioms: [propext, Quot.sound]
'OrdinalCertificates.certificate_excludes_realization' depends on axioms: [propext, Quot.sound]
'OrdinalCertificates.odd_ray_realizes_tail' depends on axioms: [propext, Quot.sound]
'OrdinalCertificates.no_all_phase_natural_rank' depends on axioms: [propext, Quot.sound]
```

SHA-256:

- `OrdinalCertificates.lean`: `712CC36D5E75C18F6060439591C392A97AF80F9B3A23A92C70198C4DEAC4D2AF`
- `ORDINAL-CHARACTERIZATION.md`: `37A7DBA53EDC4EF4FC0ACB9F606251D1DA2A342E71225DFDA523E4246A52B784`

The full ordinal theorem and necessity of natural certificates have written
proofs, but are not Lean checked. The four listed endpoints alone are covered
by this compilation receipt. The file imports only Std and has no owner-repo
dependency.

Environment incident: an earlier unqualified `lean --version` unexpectedly
invoked elan's default-toolchain download for 4.34.1. It was immediately
interrupted; directory inspection showed a `leanprover--lean4---v4.34.tmp`
directory. The successful verification used the previously installed 4.33.1
executable directly. No clean-up outside the assigned scratch folder was
attempted, and no owner-checkout file was edited.
