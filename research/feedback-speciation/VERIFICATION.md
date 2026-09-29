# Verification record

The aggregate run finished at 2026-09-25T13:01:44Z.

- Lean: 4.33.1, commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.
- Mathlib: 0df444a360eaa60ab8c11dca51a86af692955474.
- Seven source modules freshly compiled, all exit code 0.
- 72 selected endpoint axiom reports: 53 new-module reports and 19 unchanged dependency reports.
- Permitted and observed standard axioms: propext, Classical.choice, Quot.sound. No sorryAx occurred.
- One worker, per-process memory cap 4096 MB.
- Cached upstream dependency binaries were used. No clean-machine download/build or hosted CI was performed.
- The package's Lake configuration was successfully loaded by Lake and translated to TOML without dependency fetching. The translated configuration is in package/verification/lakefile.translated.toml. This checks configuration loading, not a full clean Lake build.
- Both vendored sources match their public files at immutable commit 9b7d4066ac7c27599d89ff7b76a723621bd61d00.
- The final statement and mathematical reviews are internal AI reviews. They are not external peer review, priority verification or biological validation.

The first attempted dependency-revision read encountered Git's ownership check. The runner now grants trust only to the explicitly passed Mathlib path for that single Git invocation; it does not change global configuration. All seven compilations in the successful aggregate run used the revised runner.

Running a Lake configuration directly with lean initially failed because Lake's command elaborators require the Lake loader. Loading it through lake translate-config subsequently succeeded. This was a tooling invocation error, not a theorem failure.

See the machine-readable package/verification/receipt.json and individual logs for source hashes, exact endpoint names and axiom lists. Source inventory and archive checksums accompany the review archive.
