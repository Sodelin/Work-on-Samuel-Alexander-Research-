# Review and submission material

Prepared 2026-09-25. These are drafts for the existing public-writing coordinator. No email, catalog entry, comment or journal submission was sent by this lane.

## Samuel Alexander: concise incremental handoff

Suggested subject: A checked conditional bridge from recurring parenthood to IAP

We have developed a conditional theorem using the IAP predicate from your specieslike-clusters paper. For a finite collection of demes with finite generation prefixes, continued occupancy, same-deme parent coverage and finite-window local lineage dissemination, an infinite set satisfies IAP exactly when all but finitely many of its members lie in one strongly connected component of recurring cross-deme parenthood. Sufficiently late component tails also satisfy connectivity, convexity and reflection.

The important restriction is local dissemination from every individual. Ordinary random reproduction with lineage extinction does not satisfy that all-time condition. The theorem is a deliberately restricted bridge, not an empirical species classifier. We have explicit models showing that the hypotheses are consistent and that one-way recurrent reproduction is insufficient for whole-population IAP.

The attached package contains the readable argument, exact assumptions, Lean sources, pinned dependency information, axiom reports and the closest prior-work comparisons. Structured-genealogy work by Chang and Rohde–Olson–Chang and temporal-network recurrence results are explicitly credited. We do not yet claim that the classification is novel.

Separately, the package proves a quantitative fixation bound for the affinity-bias model of Fogarty, Zhang and Feldman (2025), including arbitrarily changing admissible affinity parameters. It also contains a counterexample to the implication from persistent cultural difference to separation of neutral genetic frequencies. These make the broader genetic/regulatory/learned-behaviour idea precise at selected points, without claiming to have established that whole biological theory.

The most useful feedback would be whether the IAP classification is already known or useful, and what survival/mixing hypothesis would make an extinction-aware version biologically informative. This work was developed with AI assistance and has internal formal/statement review, but no external expert endorsement.

**Coordinator note:** consolidate with the existing correspondence; do not send a duplicate introductory message. Use immutable publication links only after the final package is integrated and checked. The separate Wong-completion task remains distinct.

## VibeMathed: candidate entry material, eligibility unresolved

**Candidate title:** Recurrent parenthood and finite/cofinite ancestry.

**Problem statement:** Given a discrete-generation pedigree partitioned into finitely many nonempty demes, with finite generation prefixes, every edge advancing one generation, every later organism having a same-deme parent, and a common finite window in which each organism reaches the entire same-deme cohort, characterize the infinite subsets satisfying Alexander's IAP axiom in terms of cross-deme parenthood occurring at arbitrarily late generations.

**Answer:** Such an infinite subset satisfies IAP if and only if it is contained in one recurring strongly connected component modulo finitely many organisms. Its representative component is unique. Component tails after one common cutoff satisfy the actual specieslike and reflection predicates.

**Problem provenance:** Newly posed source-motivated application question. Alexander's 2026 article supplies the target definitions; it does not state this precise classification as an open conjecture. Recurrence-to-reachability mechanisms are established temporal-network theory. Originality is not yet established.

**AI contribution:** AI-assisted problem formulation, proof derivation, Lean implementation and internal adversarial review. No human expert endorsement is claimed.

**Proof evidence:** The package includes complete deterministic proofs, explicit hypotheses, concrete examples, pinned Lean/Mathlib versions and compilation/axiom receipts. The conditional-probability corollary is separately labelled written-only. The formal record does not certify the empirical premises.

**Verification label:** Lean-checked, external statement audit pending. An internal second-agent audit is not the independent external statement anchoring required for the catalog's stronger label.

**Related work:** Alexander (2026); Chang (1999); Rohde, Olson and Chang (2004); Casteigts et al., Time-Varying Graphs and Dynamic Networks. The detailed comparison and search limits accompany the package.

**Eligibility decision:** Not established. [VibeMathed methodology](https://vibemathed.com/methodology) excludes mere reproofs/formalizations of established results. A [frontier](https://vibemathed.com/frontiers) requires a qualifying entry; a topic proposal alone is not such an entry. Do not submit this draft as an already validated open-problem resolution. Ask for novelty/statement review first.

## Alternative candidate for review: quantitative affinity fixation

**Statement:** In the affinity-bias recursion of Fogarty et al. 2025, suppose s>0, beta1(n),beta2(n) lie in [0,1], and the initial state contains the beneficial cultural trait in both genetic backgrounds. With r0=max(x2(0)/x1(0),x4(0)/x3(0)), the cultural deficit is at most r0/(1+s)^n, and tends to zero. The result holds for the actual recursively defined update, not only a postulated trajectory. A sharper bound follows from the odds certificate.

**Provenance:** Quantitative extension of a published model, including adaptive affinity parameters. The authors did not designate this exact rate question as an open conjecture. Prior-art assessment remains necessary; familiar convex-mixing/selection arguments may already imply it elsewhere.

**Mechanism:** Standard nonnegative-matrix order preservation; no new general contraction theorem is claimed.

**Relevance:** Gives a uniform global rate across a broad class of affinity trajectories, and cleanly identifies an initial-condition guarantee. It does not solve the paper's general nonvertical-learning direction, the different cultural-trait-bias model, or speciation.

## Material that can be put online after integration

- The complete research note, proof files and faithful scope/claim ledger.
- Compiler receipts, immutable source hashes and reproduction instructions.
- The source-linked open-question list and dated prior-work audit.
- An AI-assistance disclosure and explicit review status.

Keep source PDFs in the research evidence archive unless redistribution permissions are independently suitable. The public package need only link to official sources. Do not publish account receipts, private addresses, authentication state or unrelated user documents.

## What the Lean artifact establishes

The kernel checks the encoded deterministic implications, including their stated assumptions. It does not establish that an organism population has those properties, that DNA uniquely determines species, that cultural groups are species, that the results are original, that a journal will accept them, or that the entire Wong paper has been formalized.
