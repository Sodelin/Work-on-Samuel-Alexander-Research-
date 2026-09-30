# Preserved side-chat support verifier: provenance and fresh execution

**Fresh-run verdict: pass.** The supplied standalone verifier completed once with Node, examining 84,076 plane trees and 2,525,210 globally consistent occurrence selections. It reported zero negative anchor coefficients, zero support mismatches, and zero boundary-support failures. No retry or other verifier rerun was performed.

The preserved contribution is [sidechat_support_check.cjs](sidechat_support_check.cjs). Its full stdout, exit status, execution details, and SHA-256 hashes are saved in [SIDECHAT-SUPPORT-RECEIPT.json](SIDECHAT-SUPPORT-RECEIPT.json).

## Received provenance versus independently observed results

The parent supplied the code from the authorized handoff attributed to ephemeral chat `01a0ef7c-7cdc-7f00-a827-8a43b8ae0ffa`, reporting only XML-entity decoding and a provenance header on preservation. This is received provenance. Direct retrieval was attempted, but the chat reader returned `ephemeral threads do not support thread/turns/list`. I therefore could not independently compare the supplied file byte-for-byte with that chat's original message.

I read the supplied source, preserved it without edits, and ran that file once. These are fresh observations. Its SHA-256 before and after execution was `6cbf8660a369ef9231d2ebba55d7b9f7b930aa540bcf9379b0a190578f349dc1`. The receipt additionally pins the Node executable and hashes the captured stdout and stderr. Node returned exit code 0 with empty stderr; the verifier run took 0.938 seconds.

| Labels | Plane trees | Global occurrence selections | Quartet systems | Actual split-support systems | Anchor checks |
|---:|---:|---:|---:|---:|---:|
| 3 | 36 | 185 | 1 | 1 | 9 |
| 4 | 406 | 3,834 | 3 | 3 | 108 |
| 5 | 5,390 | 92,465 | 16 | 16 | 1,600 |
| 6 | 78,244 | 2,428,726 | 102 | 102 | 22,950 |
| Total | 84,076 | 2,525,210 | 122 across sizes | 122 across sizes | 24,667 |

Every row reported `negative=0`, `supportMismatches=0`, and `boundaryFailures=0`. The fresh totals match the handoff's stated counts.

## Bounded source review

The code enumerates every duplication mask and every ordered binary tree on its expanded tip sequence. It represents each edge away from physical tip 0 by a tip interval; the whole remaining interval also represents the edge incident to tip 0. Crucially, it explicitly chooses one occurrence of **every** label before restricting any edge.

For each such global selection, it converts original edge cuts into splits of the selected labels. Empty and full cuts are discarded, while duplicate cuts are combined. This is the correct split-set operation for deleting unselected tips and suppressing degree-two vertices. The program checks that every remaining split is circular and takes the union over complete global selections. Thus its actual-support side is extracted from selected tree edges, rather than inferred from positive anchor coefficients or the proposed boundary criterion.

It then obtains displayed quartet unions by restricting those actual splits. For each quartet-system key, it checks that every enumerated tree giving that key also gives the same actual split support. This equality is checked, not assumed by deduplication.

The anchor calculation uses twice the normalization of the preceding independent Python audit: shared-anchor entries are 2, and disjoint entries are four times the separating-topology fraction. This positive scaling preserves coefficient signs and support. The program compares the union of positive anchor positions with the actual displayed-split set, while separately rejecting any negative anchor coefficient. Under nonnegative coefficients, this union is exactly the support of the sum with positive anchor weights.

The boundary test separately compares the appropriate `bc|ad` quartet bit with actual edge-split support, treating adjacent gaps as pendant splits. It handles either orientation of the requested bipartition and the circular wraparound.

For the checked sizes, split masks need at most 15 bits and quartet masks need at most 45 bits; the former use ordinary bitwise integers and the latter use JavaScript `BigInt`. The scaled quartet entries are checked to be integral. There is no floating-point approximation in the resulting coefficient or support decisions.

## Scope

This contribution provides a complementary finite test using **actual displayed edge splits and all global selections**. It agrees with the earlier independently derived zero certificate and boundary-anchor identity. It is now preserved with reproducible code and a fresh local execution receipt.

It remains a finite result for the adjacent-copy tree representation on 3 through 6 labels. The external source-network representation, reduction to finitely many labels, and structural split lifting were not re-audited during this bounded preservation task. No Git, publication, original proof, or prior audit artifact was changed.
