# Public integration and verification boundary

The reviewed handoff ZIP has SHA-256
`89db95e0bf5fca5fb5d6951bd087badb0a032bfebb3499b528349884d144aa40`.
Every one of its 39 listed payload hashes was independently checked by the
publication coordinator. The original manifest is preserved in
[SOURCE-ARCHIVE-SHA256SUMS.txt](SOURCE-ARCHIVE-SHA256SUMS.txt).

For publication, Markdown math delimiters were converted to GitHub's protected
inline syntax and fenced displays, and text files were normalized to LF. The
exact changes in byte hashes are in [publication-transformations.json](publication-transformations.json).
The packaged local receipt describes the original archive sources. It is not
an exact-byte receipt for files whose line endings changed.

The repository's standalone audit now registers all five new modules in import
order: AncestryMixing, AncestryExamples, FeedbackDynamics, FogartyAffinity and
FogartyAffinityFixation. Their 53 selected endpoints are added to the previous
60 standalone endpoints, for 113 in 17 files. Hosted CI first builds the core and
real dependencies, then freshly compiles these modules and rejects unapproved
axioms or admitted proofs. The 19 vendored dependency reports are not counted
again as new results. [PR #6 checks](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/pull/6/checks)
show each commit's hosted result; a configured gate is not itself a passing run.

The self-contained package and its Check-All.ps1 remain available for separate
local use. The main repository CI uses its freshly built core predicate modules;
the source-origin document identifies the exact original vendored versions.

The first package retains its strong all-lineage-dissemination assumption. A
separate extinction-permitting supplement is in development and is not included
in this receipt. No new email or VibeMathed submission is implied by this archive.

To regenerate a review ZIP from this publication, first rerun `package/Check-All.ps1`
to refresh the seven-module receipt after line-ending normalization, then run
`build_review_archive.py`. The builder deliberately rejects a stale exact-byte receipt.
