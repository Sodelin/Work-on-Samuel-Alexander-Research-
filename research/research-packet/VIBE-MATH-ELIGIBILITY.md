# Vibe Math eligibility for the Alexander research packet

**Source check: 25 September 2026. No account was created and no submission was made.** The name is ambiguous. [VibeMathed](https://vibemathed.com/about) is the community-curated catalog with an [entry submission form](https://vibemathed.com/submit). [VibeMath](https://github.com/cyanseek/VibeMath) is a separate, independent, read-only frontier dashboard that currently imports VibeMathed records; its [MCP server](https://github.com/cyanseek/VibeMath#read-only-mcp-server) has no write or submission capability. A GitHub pull request to VibeMath's code repository can improve its software or evidence handling, but its current [contribution guide](https://github.com/cyanseek/VibeMath/blob/main/CONTRIBUTING.md) is not a direct route for adding an original mathematical result to the underlying catalog.

## The catalog's actual gate

[VibeMathed's methodology](https://vibemathed.com/methodology) says the inclusion test is a **precisely stated open question whose answer is now a proved or disproved theorem, with an AI model substantively in the loop**. It expressly excludes merely formalizing a result humans already proved. A genuine new bound or solved special case can be listed as a *partial result* if it advances a previously tracked question. Concurrent independent proofs of the same problem have a narrow exception when the methods are demonstrably different, the timing is close, and the authors disclose independence without claiming false priority. These are catalog-scope rules, not mathematical judgments on excluded work.

The [form](https://vibemathed.com/submit) asks for the question as posed, source URL, result, model and its actual contribution, verification and publication status, what was actually shown, and caveats. It has optional “Posed by” and “Year posed” fields; neither the form nor methodology page expressly says the original question must have appeared in a source independent of the submitting authors. For this packet, however, there **is** a dated public antecedent: the [separate AI-assisted classification manuscript, §5](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#5-universality-and-computability-in-the-witness-family) ends by asking for useful explicit bounds from each start for the fixed Thue–Morse target. That makes the prior-question gate materially stronger than a question formulated retrospectively in our current note. Whether the curators require a question to have been posed by authors entirely independent of the solving project is **not specified** publicly; their judgment remains necessary.

Submission requires Google or GitHub sign-in. The public credit is pseudonymous, and a reviewer checks the source before an entry appears. A primary source may be an arXiv paper, article, announcement, or GitHub repository with a Lean proof; the form does not require a separate code upload or a specified license for the mathematical source. The catalog's own authored data is [CC BY 4.0](https://vibemathed.com/data-license); that is not a license imposed on a submitter's proof. The [contribution page](https://vibemathed.com/contributing) asks for an author disclosure of the model's role, honest status, and a source anyone can open.

## Best candidate in this packet

The strongest candidate is the **complete Thue–Morse matching-height formula** for the target-dependent edge-labelled population in the separate [classification manuscript](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#2-an-explicit-binary-avoiding-population), together with the sharp quantitative bound, equality cases, and unconditional digit recurrence. Its §5 explicitly left useful start-dependent Thue–Morse bounds as a question, and these results answer it. The classification manuscript is dated 10 September 2026, does not name a human author in its frontmatter, and [§7](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#7-attribution-provenance-and-scope) credits a human collaborator with selecting and directing the project and Codex with the construction and proofs. Alexander's 2013 contribution was the population model, a positive theorem, and his original classification question; he did **not** author this later negative construction or its quantitative question. The current [local proof-status review](FULL-HEIGHT-STATUS-UPDATE.md) reports that the complete formula and unconditional evaluator compile and records independent source-statement and semantic checks. The local `verification/formal-audit.json` receipt in the implementation checkout reports Lean 4.33.1, 370 selected endpoints, and a permitted-axiom audit at 2026-09-25T08:13:42Z; the owner independently checked its 49 source hashes against current bytes with zero mismatches. The final combined release CI remains a separate pending gate.

Let $`H(v)`$ be the *attained* maximum number of edges in a path starting at vertex $`v`$ whose labels match the initial Thue–Morse word. Let $`t(n)\in\{0,1\}`$ be the Thue–Morse bit. Define

```math
S(h)\iff h\equiv1\pmod4\ \land\
t(\lfloor h/4\rfloor)=0\ \land\
t(\lfloor h/4\rfloor+1)=1.
```

For $`h,r\ge0`$, the proved branch values are

```math
E(h,r)=
\begin{cases}
1-(r\bmod2), & t(h)=1,\\
7-2t(h+1), & t(h)=0\text{ and }r=1,\\
(4-2t(h+1))2^r-1, & t(h)=0\text{ and }r\ne1,
\end{cases}
```

and

```math
O(h,r)=
\begin{cases}
0, & t(h)=0,\\
4\cdot2^r-1, & t(h)=1\text{ and }t(h+1)=0,\\
16\cdot2^r-3, & t(h)=t(h+1)=1\text{ and }S(h),\\
10\cdot2^r-1, & t(h)=t(h+1)=1\text{ and }\neg S(h).
\end{cases}
```

The identities are

```math
H((4h+2)2^r-2)=E(h,r),\qquad
H((4h+2)2^r-1)=O(h,r).
```

Every $`v\in\mathbb N`$ is covered: factor $`\lfloor v/2\rfloor+1=(2h+1)2^r`$, then use $`E(h,r)`$ for even $`v`$ and $`O(h,r)`$ for odd $`v`$. The local source review checks that `height_isMaximum` gives both a path attaining the claimed length and an upper bound on every matching path. `evaluate_isMaximum` connects the ten-coordinate binary-digit evaluator to this actual maximum, without assuming the formula as a premise at its endpoint. The earlier [public sharp theorem summary at the pinned baseline commit](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/425fee8c90e15656caea954ac92beaf28a5d869f/README.md#current-results) gives $`3H(v)\le8v-1`$ for $`v\ge1`$, with equality exactly at $`v=3\cdot2^n-1`$ and $`H(v)=8\cdot2^n-3`$ there; the coefficient $`8/3`$ is optimal even when a fixed additive constant is allowed. The September manuscript documents the preceding quantitative question; broader worldwide novelty remains a separate matter.

The line-graph three-root/cap-two recoding is an application of a classical directed line graph, and the three-state cellular automaton is a synthetic method demonstration. They may be useful supporting exposition or source-linked related results, but the full height formula and sharp $`8/3`$ theorem provide a stronger possible catalog entry because the September manuscript documents the quantitative question. A bounded literature search and source comparison exist in the packet, but they do not establish worldwide priority. The exact correspondence between that broad request for useful bounds and the full formula, and any earlier solutions elsewhere, need to be made reviewable for curators.

## Four distinct judgments

| Question | Current assessment |
| --- | --- |
| Mathematical correctness | The local status review reports compiling Lean endpoints, including the connection to the actual maximum, and independent source/semantic checks. A later owner-verified core 370-endpoint audit passed. Final combined integration and CI for the extension packet remain to be completed and published. |
| Originality | The quantitative theorem and complete formula are plausible research contributions beyond the cited qualitative paper. The bounded literature review is evidence, not a global novelty certificate. |
| Previously posed question | The September 2026 [classification manuscript, §5](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#5-universality-and-computability-in-the-witness-family) explicitly leaves useful Thue–Morse bounds from a fixed start open. It predates this solution. Whether the site's curators require the posing source to be independent of the solving project is **unknown**. |
| Catalog acceptance | Only VibeMathed's moderators decide after submission. A proposed entry, site listing, independent expert endorsement, and journal peer review are separate events. |

[VibeMathed's verification definitions](https://vibemathed.com/methodology#the-verification-ladder) distinguish a compiling Lean artifact from “Lean-verified,” which additionally requires independent anchoring of the formal statement against the informal question. Our packet includes independent source and semantic audits; whether they satisfy that catalog's anchoring standard is for its reviewers to assess. Its “Site-confirmed” tier may involve rerunning the artifact or certificate. Peer review is tracked on a separate publication axis. [VibeMath's claim policy](https://github.com/cyanseek/VibeMath/blob/main/CLAIM_POLICY.md) likewise treats novelty, formal statement fidelity, and peer review as distinct claims.

**Practical route:** publish a checkable research note and proof repository linking the pinned September §5 question, accurately attributing the separate manuscript and Alexander, and giving an AI-role disclosure, theorem statements, final combined build and axiom receipts, source comparison, and caveats. A VibeMathed submission could then be framed as a resolved quantitative subquestion or a partial result under its own status rules, subject to curator review of the question's scope and priority. Posting or being cataloged would not itself confer peer review or priority.
