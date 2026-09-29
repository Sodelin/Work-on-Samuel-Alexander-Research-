# Independent mathematical review

Reviewer lane: /root/pedigree_bridge. Read-only review; no compiler, finite-control rerun, source re-review, or repository edits.

The reviewer accepted the general mathematical arguments at document SHA256 `46f207c11d50c7b46caf2d863b098d27e58f41567150c600c893dd9a438eb906`: complement characterization; exact d(m,B); independent-family product; pair-event distribution separation; and repeated-block success 2^(1-m). No required correction remained after clarifying that the estimator is not claimed optimal.

The reviewer also checked the example 00,01,11: its pairwise-sharing graph is connected, although no block is shared by all three children. This distinguishes component recovery from the incoming all-three-sharing rule.

One contextual qualification was recommended for standalone reuse: ideal and actual observations in the error corollary must concern the same labeled children and the same target family partition. The fixed-model context already supplied this. The coordinating lane added those words explicitly after review, with no other mathematical change. The final document hash is recorded in MANIFEST.json.

This review is not Lean verification, a complete review of either cited paper, or evidence that the observation law follows from the marked ARG law.
