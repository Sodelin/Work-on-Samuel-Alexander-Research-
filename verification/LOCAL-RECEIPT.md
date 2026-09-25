# Local verification receipt

Run date: 24 September 2026 (America/Los_Angeles). The commands below were run from this repository's root on Windows before the initial commit. This is a local receipt; read the GitHub Actions run separately for remote CI status.

| Command or check | Observed result | Scope |
|---|---|---|
| `lake build` with Lean 4.33.1 | Exit 0; `SamuelAlexanderResearch.DegreeBounds` and top-level module built | Only arithmetic lemmas from explicit count premises. No population graph formalization. |
| `python -m unittest discover -s checks -p 'test_*.py' -v` | 6 tests passed | Includes path-history versus endpoint search for starts `0..15`, and bitset versus endpoint search for starts `1..255`. |
| `python checks/check_local_certificate.py` | `Toy rule certificate: (True, 3, None)` | Three live-output truth-table rows of a toy anisotropic rule. |
| Replayed `checks/explore.py` for starts `0..8191` | Output agreed with the saved JSON | Exact finite search, with a proved quadratic termination guard. |
| Compared `explore.path_length(v)` with the saved bitset scan for all $`1 \le v < 8192`$ | All lengths agreed | Independent frontier transitions sharing the same Thue–Morse bit function. |
| Inspected saved bitset scan for starts `1..131071` | `0` counterexamples to the proposed linear inequality, `16` equality cases, and `all_lengths_exact=true` | Finite evidence only. The bitset script reports an over-budget lower bound rather than an exact length if it finds a counterexample. |

## Saved evidence hashes

SHA-256 hashes identify the exact artifacts read during this receipt:

```text
359EDAF836ED03A831EFFAA115DE0CD6FFE3339607926A7B71B083E4CD438292  checks/scan-8192.json
0F800213A27565938C80B85E46D5F9085332985A642461746690801C80CA240A  checks/scan-bitset-131072.json.gz
FE099A1B8EAD2142434BB8B45C9F91FAA823B320560D92C70EE7BA206DDAD748  lean/SamuelAlexanderResearch/DegreeBounds.lean
B491EB6C3D206402A52EF7C181B0E69E58296513431C6A217B515580FC83E2D2  notes/THUE-MORSE-PATHS.md
```

The compressed scan contains the complete `lengths_or_lower_bounds_by_start` array. It is deterministic gzip (`mtime=0`, no embedded source filename). Decompress it with `gzip -dc` or Python's `gzip.open` to inspect the JSON. These checks do not establish literature priority or prove either conjecture.
