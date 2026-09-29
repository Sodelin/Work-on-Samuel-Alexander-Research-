"""Write a source-family continuation delta without mutating the shared ledger."""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
BASE = json.loads((HERE / 'baseline-claim-audit.json').read_text(encoding='utf-8'))
DELTA = {}


def add(ids, endpoints, detail, remaining, status=None):
    for claim_id in ids.split():
        DELTA[claim_id] = dict(endpoints=endpoints.split(), detail=detail,
                               remaining=remaining, status=status)


add('M01', 'WongMarkedRecorder.recorded_prefix_toGARG WongMarkedRecorder.projected_atLocus_iff WongMarkedRecorder.projected_unique_parent_at',
    'Every valid generated finite prefix has an acyclic interval-gARG projection with a unique local parent. Full raw lineage identities remain in the richer record.',
    'No additional foundation gap. Endpoint gARG projection can forget raw lineage identity and breakpoint information; do not identify it with the full record.')
add('M02', 'WongMarkedRecorder.projected_nonempty_annotations WongMarkedDated.realized_edge_chronology WongMarkedDated.law_ae_realize_validDated WongPedigreeBridge.pathSound_of_faithful',
    'The generated history has bounded nonempty inherited intervals and physical dates with strict chronology. Owner projection is treated explicitly and conditionally.',
    'Arbitrary metadata, inference of organism owners from an ARG, and a biological pedigree sampling model remain outside these results.')
add('M04', 'WongMarkedRecorder.split_preserves_valid WongMarkedRecorder.merge_preserves_valid WongMarkedRecorder.merge_terminal_root WongMarkedRecorder.start_one_no_event',
    'The actual recorder consumes/allocates one/two lineage identities at a split and two/one at a merger. Terminal-root and one-sample boundary cases are explicit.',
    'Old endpoint-node degree theorems still require their stated ClassicalShape hypotheses. They do not become unrestricted edge-multiplicity degree decoders.')
add('M05', 'WongMarkedRecorder.raw_records_injective WongMarkedRecorder.raw_decode_encode WongMarkedRecorder.raw_encode_decode WongMarkedRecorder.reunion_shared_endpoints WongMarkedRecorder.reunion_distinct_lineages WongMarkedRecorder.reunion_not_normalized WongMarkedRecorder.reunion_raw_decode WongMarkedRecorder.reunion_cut_retained',
    'Raw uncoalesced single-event records decode without the old Normalized restriction, including two distinct lineages with the same endpoints. Stable IDs and event logs retain the full generated record.',
    'The older normalized theorem remains scoped to its old representation. The new result covers the specified single-crossover event records and generated history; arbitrary multi-crossover/gene-conversion events remain M03.')
add('M10', 'WongMarkedRecorder.reunion_cut_retained WongMarkedRecorder.reunion_local_cut_forgotten',
    'A precise new detectability witness proves that raw records distinguish two different recombination cuts while endpoint-local semantics agree.',
    'The source broader empirical/statistical detectability discussion is not a quantified identification theorem. No detection probability or species classifier is proved.')
add('A01', '',
    'A full marked Big process now exists under the explicit continuous-breakpoint interpretation.',
    'No matching Little process or Big/Little common sample-observable law has been constructed. This family remains open.')
add('B04', 'WongMarkedLaw.finiteChoiceLaw_singleton WongMarkedLaw.cutLaw_apply WongMarkedLaw.unordered_pair_mass WongMarkedLaw.law_probability WongMarkedProcess.prefix_valid_count WongMarkedMeasurable.measurable_stoppedRecord WongMarkedMeasurable.stoppedRecordLaw_probability WongAdaptiveSelection.recorder_mark_cylinder WongMarkedDated.historyLaw_probability WongMarkedDated.history_count_time_projection',
    'The general-n marked construction now has stable lineage IDs, full-genome splits, merger pairs, event logs, Borel-measurable finite records, a probability law, an actual-recorder adaptive mark law, and a dated-history count/time projection.',
    'Checked for positive finite sample size, positive genome length, and the declared rate normalization. Breakpoints use normalized Lebesgue measure on (0,L). Figure A1 and Little use discrete links; the Big paragraph does not explicitly switch domains. Discrete-link equivalence, an all-history real-time Markov/generator theorem, and other demographic models are not proved.',
    'checked scoped result')
add('B05', 'WongMarkedProcess.law_ae_stoppedRecord WongMarkedProcess.law_ae_finite_physical_graph WongMarkedDated.realize_constant_tail WongMarkedDated.law_ae_realize_validDated',
    'Finite jump absorption and finite physical time are transferred to the actual valid marked graph; dated histories become constant after the stopping index.',
    'The stopping rule is one active lineage (GMRCA), with n=1 stopped immediately. The final dated-validity endpoint is an almost-everywhere input-space realization theorem; do not silently rename it an output-space predicate theorem. A general unstopped CTMC construction is a stronger unproved extension.',
    'checked scoped result')
add('B09', 'WongMarkedProcess.recorded_count_time_projection WongMarkedDated.history_count_time_projection',
    'Lineage counts and event times are computed from the actual recorded history and their joint law equals the already checked count/time process.',
    'A full Little-ARG effective-link trajectory and the source likelihood calculation remain unformalized. No marginal-likelihood or inference implementation is certified.')
add('D01', 'WongPedigreeBridge.iap_iff WongPedigreeBridge.reflection_iff WongPedigreeBridge.convex_iff WongPedigreeBridge.specieslike_descends WongPedigreeBridge.specieslike_iff WongPedigreeBridge.maximal_saturated_iff WongPedigreeBridge.sound_projection_does_not_determine_iap',
    'New conditional transfer and obstruction theorems connect richer inheritance histories with organism ancestry. These are mathematical extensions motivated by Wong cell/owner tagging, not claims that Wong states Alexander theorems.',
    'Finite fibres, onto ownership, ancestry reflection for every pair of representatives with different owners, saturation, and connected fibres where needed are substantial extra assumptions. Mere sound owner projection does not identify IAP or a biological species.')
add('E04', 'WongMarkedRecorder.reunion_local_cut_forgotten WongPedigreeBridge.no_specieslike_recovery_from_garg_coarsening',
    'A new local-semantic information-loss witness and a deterministic observation-fibre obstruction strengthen the existing loss examples.',
    'The generic species-like obstruction uses explicitly supplied incompatible abstract completions; it is not distributional or diploid statistical non-identifiability, nor a proof of every source simplification example.')
add('G03 H01', 'WongMarkedRecorder.reunion_valid WongMarkedRecorder.reunion_counts WongMarkedRecorder.reunion_local_cut_forgotten',
    'The immediate split/reunion control is valid in the general recorder and preserves two lineage identities while forgetting the cut under endpoint-local semantics.',
    'This control is not a replacement for the general marked construction. Full super-diamond classification and all literal source figure claims are not added here.')
add('H02', 'WongMarkedDated.history_count_time_projection',
    'The richer dated record retains the actual count/time path; its projection agrees in law with the checked process.',
    'Existing losses under simplified representations remain scoped counterexamples. The richer preservation theorem is not a converse reconstruction theorem from simplified gARGs.')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def anchor(name):
    module, decl = name.split('.', 1)
    path = ROOT / 'real' / (module + '.lean')
    lines = path.read_text(encoding='utf-8-sig').splitlines()
    found = [i for i, line in enumerate(lines, 1)
             if re.search(r'\b(?:theorem|def|instance|structure|abbrev)\s+' + re.escape(decl) + r'\b', line)]
    if len(found) != 1:
        raise RuntimeError((name, found))
    cache_path = ROOT / '.local-build' / 'wong-continuation' / (module + '.json')
    receipt = json.loads(cache_path.read_text()) if cache_path.is_file() else None
    return dict(declaration=name, path=str(path.relative_to(ROOT)).replace('\\', '/'),
                line=found[0], source_sha256=sha(path),
                module_receipt_exit_code=receipt['exit_code'] if receipt else None,
                module_receipt_source_sha256=receipt['signature']['source_sha256'] if receipt else None,
                receipt_matches_current_source=bool(receipt and receipt['signature']['source_sha256'] == sha(path)),
                module_object_sha256=receipt['object_sha256'] if receipt else None)


rows = []
for claim in BASE['claims']:
    d = DELTA.get(claim['id'])
    rows.append(dict(id=claim['id'], title=claim['title'], source_url=claim['source_url'],
                     source_locators=claim['source_locators'], baseline_status=claim['baseline_status'],
                     recommended_status=(d['status'] or claim['baseline_status']) if d else claim['baseline_status'],
                     added_evidence=d['detail'] if d else 'No continuation theorem closes an additional obligation in this family.',
                     anchors=[anchor(n) for n in d['endpoints']] if d else [],
                     remaining_obligation=d['remaining'] if d else claim['remaining_obligation']))
assert len(rows) == 52
out = dict(schema_version=1, baseline_commit=BASE['base_commit'],
           scope='Independent source-family recommendations; root owns shared coverage ledger and exact-commit combined verification.',
           source_xml_sha256=BASE['source']['primary_xml_sha256'],
           coverage_fraction=None, coverage_fraction_reason='Endpoint counts are not a paper coverage percentage.',
           claims=rows)
(HERE / 'final-coverage-delta.json').write_text(json.dumps(out, ensure_ascii=False, indent=2) + '\n', encoding='utf-8')

intro = '''# Final source-coverage delta recommendations

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
'''
table = []
for row in rows:
    refs = '; '.join(f"[{a['declaration']}](../../../../{a['path']}#L{a['line']})" for a in row['anchors'])
    cell = row['added_evidence'] + (' ' + refs + '.' if refs else '') + ' **Remaining:** ' + row['remaining_obligation']
    table.append(f"| {row['id']} — {row['title']} | {row['recommended_status']} | {cell.replace('|', '/')} |")
tail = '''

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
'''
(HERE / 'FINAL-COVERAGE-DELTA.md').write_text(intro + '\n'.join(table) + tail, encoding='utf-8')
print('Wrote all 52 family recommendations; no shared ledger or Lean source changed.')
