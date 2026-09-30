# Bounded source audit log — 2026-09-29

Scope: corrected Holtgrefe et al. definitions, canonical level-2 bloblet, NANUQ metric, positivity proof; no new field ranking or literature completeness claim.

- Initial web query: `Holtgrefe NANUQ level 2 canonical bloblet corrected paper`. Located publisher article, correction, PMC records, and author-hosted published PDF.
- Read publisher primary HTML: https://link.springer.com/article/10.1007/s11538-025-01549-4 . Targeted finds for `Lemma 4.3`, `Fig. 5`, `Proposition 2.11`, and `Definition 2.10`; targeted open around the positivity proof. Read Definitions 2.1–2.5, equations 4–12, and Lemmas 4.4–4.6.
- alphaXiv PDF queries used the exact primary author URL https://ueaeprints.uea.ac.uk/id/eprint/100829/7/Holtgrefe_etal_2025_BullMathBiol.pdf . Requested definition pages, Figure 5 canonical partition, metric 4.1, Lemmas 4.5–4.6, and then missing pages 16, 17, 21 plus quartet indicator/tree-edge formulas. Returned raw page text, not an answer treated as evidence without source pages.
- Verified correction https://link.springer.com/article/10.1007/s11538-025-01564-5 . It adds Figure 12b only and states results are unchanged.
- Browser opening the university PDF failed as restricted URL. Publisher Download PDF link returned an internal error. Figure 5 link was discoverable at https://media.springernature.com/lw685/springer-static/image/art%3A10.1007%2Fs11538-025-01549-4/MediaObjects/11538_2025_1549_Fig5_HTML.png . Retrieval returned 3,038 bytes of HTML, not a valid PNG; image viewing failed. Renamed the receipt `publisher-figure5-response.html` to avoid representing it as a downloaded figure. No visual claim made.
- Ordinary sandbox command launch failed with `helper_unknown_error: apply deny-read ACLs`. Narrow escalated commands succeeded for public-source retrieval, task-file reads, and task-owned exact calculations. No installation or external write.
- Implemented an independent six-leaf graph fixture. `python source/fixture.py` passed degree/topological checks, 15 quartet rows, four switchings, all coefficient/support assertions, and exact metric reconstruction.
- Read parent `../exact_networks.py`; source semantics and one-blob generator agreed. Compared all 15 metric pairs and all 90 quartet-pair rho values after relabeling: exact match.
- Independent finite reduction evaluator `python source/anchor_audit.py`: 205 templates, 4,313 anchors, 100,787 coefficients, all nonnegative; support assertions passed. Used four-point path-length extraction rather than parent split restriction.
- `python source/cluster_bridge_check.py`: exact cluster identity passed all 45 representative pairs across 7-, 8-, and 10-taxon expansions. One size-three cluster has a nonzero within-cluster term, so the test does not only exercise zero H cases.

Files written only under this source directory. The source paper and parent implementation were not modified. No broad follow-up search or publication action performed.
