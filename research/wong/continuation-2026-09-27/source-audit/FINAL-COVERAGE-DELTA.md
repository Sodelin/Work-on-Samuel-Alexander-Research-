# Final source-coverage delta recommendations

**Integration supplement:** the subsequently checked `WongMarkedSupport.measurableSet_valid`
and `WongDatedSupport.measurable_validDated` discharge the support-predicate
measurability premise. `WongDatedSupport.historyLaw_ae_validDated` now proves
validity directly under the output history law. The earlier input-space
endpoint below keeps its original name and scope. Also,
`WongPedigreeRobust.iap_iff_of_finite_projection_errors` weakens exact ancestry
reflection to finitely many per-representative ancestry disagreements for IAP
alone. These additions do not close any additional whole-paper family.

This is the independent source lane's recommendation for integrating the
continuation into the shared ledger. It covers all 52 baseline claim families.
The original exact-source inventory remains in `BASELINE-AUDIT.md` and
`baseline-claim-audit.json`. The root integration lane owns the shared ledger,
the final commit, and combined verification. No endpoint count is a coverage
percentage.

The main changes are B04 and B05: the construction now includes the actual
marked recorder, its natural measurable encoding, adaptive choices, dated
history law, and a proved count/time projection. Both can be recorded as
**checked scoped results under the explicit continuous-breakpoint
interpretation**. This is not a claim that the entire paper is formalized.
The source's Big paragraph is at `//sec[@id="app2"]/p[5]`, journal page 13
(one-based PDF page 14); MathML IM38/IM39 give choose(k,2) and k*rho. Figure A1
and the Little process explicitly use discrete links. The Big paragraph's
uniform interior position does not explicitly announce a switch of coordinate
model, so the continuous interpretation must remain visible.

The exact new endpoint names below are linked to their current source lines.
The machine companion records source hashes and whether the available local
module receipt matches each current source. These local module receipts do
not replace the final exact-commit combined check.

| Family | Recommended status | Added evidence and remaining boundary |
|---|---|---|
| M01 — Finite interval gARG | checked scoped result | Every valid generated finite prefix has an acyclic interval-gARG projection with a unique local parent. Full raw lineage identities remain in the richer record. [WongMarkedRecorder.recorded_prefix_toGARG](../../../../real/WongMarkedRecorder.lean#L393); [WongMarkedRecorder.projected_atLocus_iff](../../../../real/WongMarkedRecorder.lean#L403); [WongMarkedRecorder.projected_unique_parent_at](../../../../real/WongMarkedRecorder.lean#L424). **Remaining:** No additional foundation gap. Endpoint gARG projection can forget raw lineage identity and breakpoint information; do not identify it with the full record. |
| M02 — Genome bounds, dates, owners and metadata | partial | The generated history has bounded nonempty inherited intervals and physical dates with strict chronology. Owner projection is treated explicitly and conditionally. [WongMarkedRecorder.projected_nonempty_annotations](../../../../real/WongMarkedRecorder.lean#L418); [WongMarkedDated.realized_edge_chronology](../../../../real/WongMarkedDated.lean#L142); [WongMarkedDated.law_ae_realize_validDated](../../../../real/WongMarkedDated.lean#L183); [WongPedigreeBridge.pathSound_of_faithful](../../../../real/WongPedigreeBridge.lean#L43). **Remaining:** Arbitrary metadata, inference of organism owners from an ARG, and a biological pedigree sampling model remain outside these results. |
| M03 — Multiple crossovers and gene conversion | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Encode a finite partition with a selected parent per cell; prove routing equivalence; instantiate two-cut gene conversion and multiple crossovers. |
| M04 — Classical event arity and parent ordering | partial | The actual recorder consumes/allocates one/two lineage identities at a split and two/one at a merger. Terminal-root and one-sample boundary cases are explicit. [WongMarkedRecorder.split_preserves_valid](../../../../real/WongMarkedRecorder.lean#L261); [WongMarkedRecorder.merge_preserves_valid](../../../../real/WongMarkedRecorder.lean#L288); [WongMarkedRecorder.merge_terminal_root](../../../../real/WongMarkedRecorder.lean#L646); [WongMarkedRecorder.start_one_no_event](../../../../real/WongMarkedRecorder.lean#L625). **Remaining:** Old endpoint-node degree theorems still require their stated ClassicalShape hypotheses. They do not become unrestricted edge-multiplicity degree decoders. |
| M05 — Lossless event encoding before simplification | checked scoped result | Raw uncoalesced single-event records decode without the old Normalized restriction, including two distinct lineages with the same endpoints. Stable IDs and event logs retain the full generated record. [WongMarkedRecorder.raw_records_injective](../../../../real/WongMarkedRecorder.lean#L543); [WongMarkedRecorder.raw_decode_encode](../../../../real/WongMarkedRecorder.lean#L596); [WongMarkedRecorder.raw_encode_decode](../../../../real/WongMarkedRecorder.lean#L601); [WongMarkedRecorder.reunion_shared_endpoints](../../../../real/WongMarkedRecorder.lean#L705); [WongMarkedRecorder.reunion_distinct_lineages](../../../../real/WongMarkedRecorder.lean#L710); [WongMarkedRecorder.reunion_not_normalized](../../../../real/WongMarkedRecorder.lean#L718); [WongMarkedRecorder.reunion_raw_decode](../../../../real/WongMarkedRecorder.lean#L732); [WongMarkedRecorder.reunion_cut_retained](../../../../real/WongMarkedRecorder.lean#L737). **Remaining:** The older normalized theorem remains scoped to its old representation. The new result covers the specified single-crossover event records and generated history; arbitrary multi-crossover/gene-conversion events remain M03. |
| M06 — Sample-support restriction | checked scoped result | No continuation theorem closes an additional obligation in this family. **Remaining:** Preserve the exact operation name. It keeps ancestors above local MRCAs, unlike M07. |
| M07 — Fig.3 local-MRCA truncation | checked scoped result | No continuation theorem closes an additional obligation in this family. **Remaining:** The deterministic stopping semantics is closed. Literal Figure 3 data and stochastic sample-set/count transition semantics are not supplied; B01-B06 remain separate. |
| M08 — Tables and incremental local-tree recovery | partial | No continuation theorem closes an additional obligation in this family. **Remaining:** Define executable sorted tables and across-coordinate remove/insert updates, prove equivalence to direct extraction and analyze record scanning, functional-cache evaluation, actual array allocation and machine costs. The new per-coordinate abstract count theorem does not prove those costs. |
| M09 — Unresolved event order in coarse topology | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define valid refinements and observation fibres; construct different event orders with one coarse gARG. |
| M10 — Recombination detectability | source clarification required | A precise new detectability witness proves that raw records distinguish two different recombination cuts while endpoint-local semantics agree. [WongMarkedRecorder.reunion_cut_retained](../../../../real/WongMarkedRecorder.lean#L737); [WongMarkedRecorder.reunion_local_cut_forgotten](../../../../real/WongMarkedRecorder.lean#L746). **Remaining:** The source broader empirical/statistical detectability discussion is not a quantified identification theorem. No detection probability or species classifier is proved. |
| M11 — Tree-metric costs and overlooked shared identity | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Choose the actual metric/algorithm and prove its cost; separately give equal local observations with different shared internal identities. |
| M12 — Scalability, software use and standardization | empirical reproduction open | No continuation theorem closes an additional obligation in this family. **Remaining:** Record historical versions, cited benchmarks and interoperability examples; document recommendation as judgment. |
| M13 — Uncertainty and improved global benchmarks | research agenda | No continuation theorem closes an additional obligation in this family. **Remaining:** Keep explicit source open-question inventory and needed definitions; assess any new theorem independently. |
| A01 — Big/Little common-observable law | open | A full marked Big process now exists under the explicit continuous-breakpoint interpretation. **Remaining:** No matching Little process or Big/Little common sample-observable law has been constructed. This family remains open. |
| A02 — NP-hard minimum recombination reconstruction | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Recover exact decision problem, mutation assumptions, input encoding and threshold; prove polynomial reduction with yes/no equivalence. |
| A03 — Coalescent, ASG and inference history | context documented | No continuation theorem closes an additional obligation in this family. **Remaining:** If claiming mathematical coverage of the ASG description, define random graph and tree-selection kernel. Historical mentions do not require proving every cited article. |
| B01 — Little-ARG lineage state | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define ordered segment/sample-set state and retired coordinates; prove initialization, sample-partition and mass invariants. |
| B02 — Effective links and splitting | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Enumerate effective links and prove count formula; uniform split preserves exact ancestral segments and counts. |
| B03 — Merge and retire fully-coalesced material | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Prove canonical overlay, additive overlap, preserved nonoverlap and correct retirement/empty-lineage deletion. |
| B04 — Big-ARG generator and event recording | checked scoped result | The general-n marked construction now has stable lineage IDs, full-genome splits, merger pairs, event logs, Borel-measurable finite records, a probability law, an actual-recorder adaptive mark law, and a dated-history count/time projection. [WongMarkedLaw.finiteChoiceLaw_singleton](../../../../real/WongMarkedLaw.lean#L67); [WongMarkedLaw.cutLaw_apply](../../../../real/WongMarkedLaw.lean#L95); [WongMarkedLaw.unordered_pair_mass](../../../../real/WongMarkedLaw.lean#L141); [WongMarkedLaw.law_probability](../../../../real/WongMarkedLaw.lean#L204); [WongMarkedProcess.prefix_valid_count](../../../../real/WongMarkedProcess.lean#L92); [WongMarkedMeasurable.measurable_stoppedRecord](../../../../real/WongMarkedMeasurable.lean#L347); [WongMarkedMeasurable.stoppedRecordLaw_probability](../../../../real/WongMarkedMeasurable.lean#L370); [WongAdaptiveSelection.recorder_mark_cylinder](../../../../real/WongAdaptiveSelection.lean#L267); [WongMarkedDated.historyLaw_probability](../../../../real/WongMarkedDated.lean#L90); [WongMarkedDated.history_count_time_projection](../../../../real/WongMarkedDated.lean#L95). **Remaining:** Checked for positive finite sample size, positive genome length, and the declared rate normalization. Breakpoints use normalized Lebesgue measure on (0,L). Figure A1 and Little use discrete links; the Big paragraph does not explicitly switch domains. Discrete-link equivalence, an all-history real-time Markov/generator theorem, and other demographic models are not proved. |
| B05 — Big nonexplosion and almost-sure absorption | checked scoped result | Finite jump absorption and finite physical time are transferred to the actual valid marked graph; dated histories become constant after the stopping index. [WongMarkedProcess.law_ae_stoppedRecord](../../../../real/WongMarkedProcess.lean#L151); [WongMarkedProcess.law_ae_finite_physical_graph](../../../../real/WongMarkedProcess.lean#L159); [WongMarkedDated.realize_constant_tail](../../../../real/WongMarkedDated.lean#L114); [WongMarkedDated.law_ae_realize_validDated](../../../../real/WongMarkedDated.lean#L183). **Remaining:** The stopping rule is one active lineage (GMRCA), with n=1 stopped immediately. The final dated-validity endpoint is an almost-everywhere input-space realization theorem; do not silently rename it an output-space predicate theorem. A general unstopped CTMC construction is a stronger unproved extension. |
| B06 — Little-ARG absorption | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Prove nonexplosion and almost-sure retirement of all coordinates, directly or via a justified coupling. |
| B07 — Big exponential event growth | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Resolve expectation, event type, asymptotic regime and rate convention. Literal rates suggest a factor-of-two exponential mismatch; prove the correctly matched result. |
| B08 — Little quadratic event growth | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Find precise bound, expectation and discrete/continuous regime; state dependence on n,m,rho and event types; prove it. |
| B09 — Timed lineage/link counts and likelihood | partial | Lineage counts and event times are computed from the actual recorded history and their joint law equals the already checked count/time process. [WongMarkedProcess.recorded_count_time_projection](../../../../real/WongMarkedProcess.lean#L248); [WongMarkedDated.history_count_time_projection](../../../../real/WongMarkedDated.lean#L95). **Remaining:** A full Little-ARG effective-link trajectory and the source likelihood calculation remain unformalized. No marginal-likelihood or inference implementation is certified. |
| B10 — Extrinsic paired-parent timing convention | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define enriched timed nodes and grouping; prove recovery of event partition and k(t),nu(t), including gaps. |
| C01 — Matrix moves and along-genome SPR | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define named mutation/coalescence/recombination moves and prove compatibility of constructed ARGs; formalize event-to-SPR relation including invisible events. |
| C02 — Monte Carlo, approximations and consensus | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Obtain precise primary target/approximation and filtering/consensus rules for any claimed formal coverage; prove a clearly named property. |
| C03 — Historical inference scalability | empirical reproduction open | No continuation theorem closes an additional obligation in this family. **Remaining:** Record historical versions, hardware, sample/sequence sizes and cited experiments; reproduce if asserting independent confirmation. |
| D01 — Cell-lineage tagging and owner projection | partial | New conditional transfer and obstruction theorems connect richer inheritance histories with organism ancestry. These are mathematical extensions motivated by Wong cell/owner tagging, not claims that Wong states Alexander theorems. [WongPedigreeBridge.iap_iff](../../../../real/WongPedigreeBridge.lean#L125); [WongPedigreeBridge.reflection_iff](../../../../real/WongPedigreeBridge.lean#L142); [WongPedigreeBridge.convex_iff](../../../../real/WongPedigreeBridge.lean#L217); [WongPedigreeBridge.specieslike_descends](../../../../real/WongPedigreeBridge.lean#L258); [WongPedigreeBridge.specieslike_iff](../../../../real/WongPedigreeBridge.lean#L332); [WongPedigreeBridge.maximal_saturated_iff](../../../../real/WongPedigreeBridge.lean#L352); [WongPedigreeBridge.sound_projection_does_not_determine_iap](../../../../real/WongPedigreeBridge.lean#L421). **Remaining:** Finite fibres, onto ownership, ancestry reflection for every pair of representatives with different owners, saturation, and connected fibres where needed are substantial extra assumptions. Mere sound owner projection does not identify IAP or a biological species. |
| D02 — Mutation information resolving cellular bifurcations | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define binary cell lineage and explicit sufficient mutation observations; prove distinction of the relevant branch order and give failures with inadequate data. |
| E01 — Executable sample-to-root extraction | checked scoped result | No continuation theorem closes an additional obligation in this family. **Remaining:** The sample-rootward algorithm and abstract write/check/lookup counts are checked. Canonical finite interval semantics is now supplied by E03/G06; executable whole-exporter, machine-array storage, concrete scanning/runtime costs and external tskit conformance remain open. MRCA truncation is a separate operation. |
| E02 — Local-array reconstruction | partial | No continuation theorem closes an additional obligation in this family. **Remaining:** Canonical interval semantics is established. A fully executable array-to-record exporter, byte-format round trip and persistent metadata packaging remain open. All-node recovery is a different observation. |
| E03 — Executable finite interval serialization | partial | No continuation theorem closes an additional obligation in this family. **Remaining:** Implement and verify computable endpoint/cell enumeration, activity tests and record emission, then specify the external serialization format and parser. The existing graph adapter is noncomputable; only its list-merge component executes. |
| E04 — Information loss from unlabelled or suppressed trees | partial | A new local-semantic information-loss witness and a deterministic observation-fibre obstruction strengthen the existing loss examples. [WongMarkedRecorder.reunion_local_cut_forgotten](../../../../real/WongMarkedRecorder.lean#L746); [WongPedigreeBridge.no_specieslike_recovery_from_garg_coarsening](../../../../real/WongPedigreeBridge.lean#L464). **Remaining:** The generic species-like obstruction uses explicitly supplied incompatible abstract completions; it is not distributional or diploid statistical non-identifiability, nor a proof of every source simplification example. |
| E05 — NP-hard SPR reconstruction | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Select exact rooted/unrooted primary theorem, tree class, labels, moves and threshold; prove polynomial reduction. |
| E06 — SPR with shared internal identities | research agenda | No continuation theorem closes an additional obligation in this family. **Remaining:** State which nodes are shared and which moves are allowed; keep a separate research question. |
| F01 — Local arity bounds and presence | checked scoped result | No continuation theorem closes an additional obligation in this family. **Remaining:** Connect executable sample arrays to these counts after E01; preserve distinction between absence and local unary presence. |
| F02 — Locally unary examples and sampled ancestors | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Instantiate varying arity, graph-binary/always-unary, pass-through, recombinant and sampled-ancestor examples; prove counts and safe retention behavior. |
| G01 — Wright-Fisher generation of the example | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define generations, random parent choices, recombination and overlap coalescence; prove finite generated prefixes are gARGs and reproduce the instance separately. |
| G02 — Span and coalescent fraction | open | No continuation theorem closes an additional obligation in this family. **Remaining:** Define coordinate measure, local presence, coalescence set and fraction; prove bounds, invariance under partition changes and zero/one cases. |
| G03 — Diamonds and super-diamonds | partial | The immediate split/reunion control is valid in the general recorder and preserves two lineage identities while forgetting the cut under endpoint-local semantics. [WongMarkedRecorder.reunion_valid](../../../../real/WongMarkedRecorder.lean#L672); [WongMarkedRecorder.reunion_counts](../../../../real/WongMarkedRecorder.lean#L685); [WongMarkedRecorder.reunion_local_cut_forgotten](../../../../real/WongMarkedRecorder.lean#L746). **Remaining:** This control is not a replacement for the general marked construction. Full super-diamond classification and all literal source figure claims are not added here. |
| G04 — Remove vertices that never coalesce locally | partial | No continuation theorem closes an additional obligation in this family. **Remaining:** The Figure5c stage removes nodes never locally coalescent across the entire genome. Derive and verify that global eligibility rule separately; the new cell-dependent rule targets Figure5d-type contraction and does not itself identify the global stage. |
| G05 — Coordinate-dependent unary bypass | checked scoped result | No continuation theorem closes an additional obligation in this family. **Remaining:** The source-relevant deterministic normal-form theorem is established. Full pipeline idempotence, an executable implementation, intermediate global Figure 5c eligibility and literal Figure 5 replication remain separate. The final fixed-point clause is interval storage only. |
| G06 — Adjacent equal-output coalescing | checked scoped result | No continuation theorem closes an additional obligation in this family. **Remaining:** Canonical interval-record semantics and storage idempotence are closed. An executable whole-GARG exporter, a separately encoded maximal-run tree table and whole-simplification idempotence are not established here. |
| G07 — External simplify implementations | empirical reproduction open | No continuation theorem closes an additional obligation in this family. **Remaining:** Pin software versions/configurations and validate conformance through adapters/examples; full implementation verification is a distinct project. |
| H01 — Supported diamond loses breakpoint information | checked scoped result | The immediate split/reunion control is valid in the general recorder and preserves two lineage identities while forgetting the cut under endpoint-local semantics. [WongMarkedRecorder.reunion_valid](../../../../real/WongMarkedRecorder.lean#L672); [WongMarkedRecorder.reunion_counts](../../../../real/WongMarkedRecorder.lean#L685); [WongMarkedRecorder.reunion_local_cut_forgotten](../../../../real/WongMarkedRecorder.lean#L746). **Remaining:** This control is not a replacement for the general marked construction. Full super-diamond classification and all literal source figure claims are not added here. |
| H02 — Timing and lineage precision loss | partial | The richer dated record retains the actual count/time path; its projection agrees in law with the checked process. [WongMarkedDated.history_count_time_projection](../../../../real/WongMarkedDated.lean#L95). **Remaining:** Existing losses under simplified representations remain scoped counterexamples. The richer preservation theorem is not a converse reconstruction theorem from simplified gARGs. |
| H03 — Literal Figure 5 tree counts and boundaries | empirical reproduction open | No continuation theorem closes an additional obligation in this family. **Remaining:** Load published/supplementary intervals, validate graphs, apply specified transformations and compute counts/lost boundaries. |
| I01 — Four inference outputs and exact inputs | empirical reproduction open | No continuation theorem closes an additional obligation in this family. **Remaining:** Pin paper code/data/output hashes, versions/seeds; parse and validate actual gARGs. Distinguish archived-output validation from inference rerun. |
| I02 — Seven-recombination parsimony optimum | source clarification required | No continuation theorem closes an additional obligation in this family. **Remaining:** Recover exact data/model; certify a compatible 7-event history and rule out all histories with fewer events using a sound certificate or imported theorem. |
| I03 — Figure 4 metrics and persistent clade claims | empirical reproduction open | No continuation theorem closes an additional obligation in this family. **Remaining:** Compute all named metrics from pinned outputs: shared breakpoints, parent counts, coalescent spans, branch order, persistent nodes/edges and named clade across full span. |

## Probability-law boundary

`WongAdaptiveSelection.recorder_mark_cylinder` is the concrete source-law
endpoint, not just a stored-coordinate marginal. For every measurable event
H in the whole count-clock path and actual t-event record, it proves the
cylinder law of the next mark selected by the actual frontier. Its proof
derives frontier adaptedness from the actual recursion, then uses joint
independence of strict earlier rows and product integration. All 14 printed
adaptive endpoints passed with only `propext`, `Classical.choice`, and
`Quot.sound`; the final module receipt is `WongAdaptiveSelection-final.json`.
The whole count-clock path is used only to condition the spatial-mark law.
An all-history CTMC/generator characterization, or an exponential waiting-time
claim under a sigma-field revealing all future clocks, is not proved here.

The correct final dated-validity endpoint is
`WongMarkedDated.law_ae_realize_validDated`: almost every input realizes a valid
dated history. The graph law and measurable projection are proved separately.
Use those actual theorem statements; do not silently replace them by an
unproved output-predicate measurability assertion.

The shared checker summary was overwritten by the following Dated check
before it was copied. `shared-dated-closure-receipt.json` is therefore labelled
as that Dated receipt. The adaptive module-specific final log and receipt
remain correct. Root should retain uniquely named combined receipts at its
exact commit to avoid this shared-summary race.

## B07 exact checkpoint and shortest next route

Appendix B paragraph 6 gives Big expected event growth `O(exp(rho))` and
Little growth `O(rho^2)` (MathML IM41/IM42). It does not provide a fully
quantified cost variable, starting-size regime, normalization, or proof in
that paragraph. With the literal preceding rates, the count-chain ratio is
theta=2*rho. The audited source does not by itself justify calling the stated
bound an erratum or replacing it by an `O(exp(2*rho))` theorem.

The shortest rigorous continuation is first to define the cost precisely,
for example total event count J before the first hit of one, with fixed
initial n>=2 and rho tending to infinity. Conditional on finite expectations,
the desired first-step recurrence for d_k = E_k[J] - E_(k-1)[J] is

```
(k-1) d_k - 2*rho d_(k+1) = (k-1) + 2*rho,
E_1[J] = 0.
```

The recurrence alone is not uniqueness. A route avoiding undefined
differences of infinite expectations is to begin with stopped finite-state
approximations and monotone convergence, or characterize the minimal
nonnegative expected crossing-cost solution first. Prove finiteness before
using the displayed differences. Only then derive asymptotic bounds in the declared
regime and compare normalizations with the cited primary literature. This
recurrence and those expectation/asymptotic lemmas are an exact unproved
checkpoint, not a claimed Lean result or a novelty claim. Little growth
additionally needs the missing Little process and an explicit observable
cost. Almost-sure finite absorption does not establish finite expectation.

## Biological bridge boundary

The Alexander transfer theorems are new conditional mathematical connections,
not implicit claims in Wong. They require the declared ownership, finite
fibre, ancestry-reflection, saturation, and connectivity assumptions. The
counterexamples rule out inference from mere sound projection. Deterministic
observation non-recovery does not assert equality of statistical sampling
distributions. Neither a pedigree nor an ARG alone classifies a biological
species.
