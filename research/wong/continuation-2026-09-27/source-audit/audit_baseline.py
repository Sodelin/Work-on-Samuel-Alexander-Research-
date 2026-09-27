"""Rebuild the source/coverage inventory without invoking Lean or changing Git.

All repository inputs are read from BASE, not the possibly dirty checkout.
The XML is an independently preserved primary-source input checked by SHA256.
Run from any directory with: python audit_baseline.py --source-xml PATH
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import xml.etree.ElementTree as ET
from collections import Counter
from pathlib import Path

BASE = "01db8c4cbb82000950ff7d3e7252b5438416c7c3"
XML_SHA256 = "2b77c349f39d2885b3e36d3bcab639a7ef3b9c6217263031aa4bc8f1c2a0d05e"
DEFAULT_XML = Path(__file__).resolve().parent / "PMC11373519-fullText.xml"
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[3]
REPO_URL = "https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-"
PDF_URL = "https://www.pure.ed.ac.uk/ws/portalfiles/portal/458588307/iyae100.pdf"

# Exact XML paragraph locators, refined from the older section-only ledger.
PARAS = {
    "M01": [("iyae100-s1", [2, 3])],
    "M02": [("iyae100-s1", [1, 3, 4, 5])],
    "M03": [("iyae100-s1", [2]), ("iyae100-s2", [2])],
    "M04": [("iyae100-s2", [1])],
    "M05": [("iyae100-s3", [4])],
    "M06": [("iyae100-s3", [1, 2, 3])],
    "M07": [("iyae100-s3", [5])],
    "M08": [("iyae100-s5", [1])],
    "M09": [("iyae100-s2", [3]), ("iyae100-s6", [1])],
    "M10": [("iyae100-s4", [3])],
    "M11": [("iyae100-s6", [2])],
    "M12": [("iyae100-s5", [2]), ("iyae100-s6", [3, 4])],
    "M13": [("iyae100-s6", [1, 2])],
    "A01": [("app1", [1]), ("app2", [1])],
    "A02": [("app1", [5])],
    "A03": [("app1", [1, 3, 4, 6])],
    "B01": [("app2", [2])],
    "B02": [("app2", [2, 3])],
    "B03": [("app2", [4])],
    "B04": [("app2", [5])],
    "B05": [("app2", [5])],
    "B06": [("app2", [4])],
    "B07": [("app2", [6])],
    "B08": [("app2", [6])],
    "B09": [("app2", [7])],
    "B10": [("app2", [7])],
    "C01": [("app3", [1])],
    "C02": [("app3", [2, 3])],
    "C03": [("app3", [2])],
    "D01": [("app4", [1])],
    "D02": [("app4", [2])],
    "E01": [("app5", [2])],
    "E02": [("app5", [3])],
    "E03": [("app5", [3])],
    "E04": [("app5", [4, 5, 6])],
    "E05": [("app5", [7])],
    "E06": [("app5", [7])],
    "F01": [("app6", [1])],
    "F02": [("app6", [2, 3, 4])],
    "G01": [("app7", [2])],
    "G02": [("app7", [3])],
    "G03": [("app7", [5])],
    "G04": [("app7", [6])],
    "G05": [("app7", [7])],
    "G06": [("app7", [7]), ("app8", [2, 4])],
    "G07": [("iyae100-s3", [3]), ("app7", [1, 2])],
    "H01": [("app8", [1, 2])],
    "H02": [("app8", [3, 4]), ("app2", [7])],
    "H03": [("app8", [2, 3, 4])],
    "I01": [("app9", [1, 2, 3])],
    "I02": [("app9", [4])],
    "I03": [("app9", [4, 5, 6])],
}

# A nonempty entry is an anchor for the scoped result or a clearly identified
# prerequisite, never evidence that the whole claim is proved.
ANCHORS = {
    "M01": ["WongGARG.GARG", "WongGARG.GARG.locus_acyclic", "WongGARG.GARG.topology_iff_erased"],
    "M02": ["WongGARG.GARG.exists_finite_topological_numbering", "WongGARG.GARG.locus_path_projects", "HistoryProjection.path_projects"],
    "M03": ["WongEventEncoding.ParentSpec", "WongEventEncoding.EventGraph.encoded_atLocus"],
    "M04": ["WongEventDecoding.encoded_degrees", "WongEventDecoding.classical_kind_unique", "WongEventDecoding.classical_encoded_sample_iff"],
    "M05": ["WongEventDecoding.Normalized", "WongEventDecoding.normalized_records_injective", "WongEventDecoding.Graph.graph_identified", "WongEventDecoding.equal_parent_crossover_same_local"],
    "M06": ["AncestralRestriction.locus_sample_path_iff", "AncestralRestriction.restriction_idempotent", "WongGARG.GARG.extracted_eq_local_iff_sampleSupported"],
    "M07": ["WongMRCATruncation.exists_unique_mrca", "WongMRCATruncation.finite_mrca_truncation", "WongMRCATruncation.truncate_mrca_paths"],
    "M08": ["WongMemoizedTracing.run_write_accounting", "WongMemoizedTracing.memoized_cost_bounds"],
    "M09": ["AncestryContraction.retained_path_iff"],
    "M10": [], "M11": [], "M12": [], "M13": [], "A01": [], "A02": [], "A03": [],
    "B01": ["WongGARG.GARG"], "B02": [],
    "B03": ["WongMRCATruncation.truncation_iff_cut_above"],
    "B04": ["WongCountChain.pathLaw", "WongBigARGAbsorption.literal_up_kernel_mass", "WongBigARGAbsorption.literal_down_kernel_mass", "WongWaitingTimes.joint_holding_observation", "WongWaitingTimes.holdingLaw_survival_cylinder"],
    "B05": ["WongBigARGAbsorption.ae_finite_jump_absorption", "WongWaitingTimes.literal_rates_ae_finite_physical_absorption", "WongWaitingTimes.physicalAbsorptionTime_of_no_hit"],
    "B06": [], "B07": [], "B08": [],
    "B09": ["WongTimedHistory.no_exact_time_decoder", "WongTimedHistory.no_exact_lineage_decoder", "WongTimedHistory.counted_edge_iff"],
    "B10": [], "C01": [], "C02": [], "C03": [],
    "D01": ["HistoryProjection.path_projects", "HistoryProjection.path_projects_strict_of_distinct_owners"],
    "D02": [],
    "E01": ["WongSampleTracing.actual_garg_extraction", "WongRecordTracing.records_to_sample_array", "WongMemoizedTracing.records_to_memoized_sample_array"],
    "E02": ["WongRecordTracing.records_round_trip_iff", "WongMemoizedTracing.memoized_records_round_trip_iff", "WongIntervalCanonicalization.canonicalize_semantic_unique"],
    "E03": ["WongIntervalCanonicalization.mergeAdjacent_covers", "WongIntervalCanonicalization.canonicalize_idempotent"],
    "E04": ["WongDiamond.diamond_cutoff_information_loss", "WongExamples.finite_garg_sample_reconstruction_boundary"],
    "E05": [], "E06": [],
    "F01": ["WongLocalArity.local_arity_le_graph_arity", "WongLocalArity.graph_unary_present_locally_unary"],
    "F02": ["WongLocalSimplification.suppressed_at_most_one_child", "WongLocalSimplification.samples_and_branching_representable"],
    "G01": [], "G02": [],
    "G03": ["WongDiamond.same_finite_output_hides_cutoff", "AncestryContraction.retained_path_iff"],
    "G04": ["WongLocalSimplification.KeepSamplesAndBranching", "WongLocalSimplification.samples_and_branching_cellwise"],
    "G05": ["WongSimplificationNormalForm.retained_nonsample_branches", "WongSimplificationNormalForm.canonical_resolved_normal_form"],
    "G06": ["WongIntervalCanonicalization.canonicalize_semantic_unique", "WongIntervalCanonicalization.canonicalize_idempotent"],
    "G07": [],
    "H01": ["WongDiamond.diamond_cutoff_information_loss", "WongDiamond.same_finite_output_hides_cutoff"],
    "H02": ["WongTimedHistory.observation_independent", "WongTimedHistory.lineage_counts_differ"],
    "H03": [], "I01": [], "I02": [],
    "I03": ["WongLocalArity.local_arity_le_graph_arity"],
}

DIFFERENCES = {
    "M04": "The degree decoder counts endpoint nodes. A raw event multigraph with parallel lineage edges needs an edge-identity degree convention; the strict ClassicalShape result must not be applied merely from source binary event arity.",
    "M05": "The normalized inverse is valid on its stated range, but distinct lineage edges may share endpoints after immediate reunion. Full source correspondence needs lineage/port identities or an explicit restriction. The older 'no further gap' remaining-target wording does not cover this obstruction.",
    "A01": "The statement 'No coupling or probability-law model' is too broad after the count/clock additions: a count/clock law exists, while a matched Big/Little sample-observable law remains absent.",
    "B01": "The source carries integer ancestral sample counts per segment. The ledger asks for actual sample sets, a stronger sufficient refinement; mark that addition as a chosen invariant rather than a source quotation.",
    "B04": "Use actual lineage identities and distinguish discrete links from continuous breakpoints. The source's Figure A1 is explicitly discrete; Big prose does not explicitly announce a coordinate-model change. Either parameterize the breakpoint law or name the continuous interpretation.",
    "B05": "Finite jump index and finite physical time are already proved for the count/clock law. Only transfer to a valid marked recording process is needed for the stated source absorption claim; a full real-time Markov-state theorem is a separate stronger development.",
    "B07": "The source gives O(exp(rho)) without a fully quantified cost variable/regime. With literal rates choose(k,2), k*rho the normalized ratio is 2*rho. No erratum or O(exp(2*rho)) theorem has been established by this audit.",
    "E02": "Appendix E's informal all-gARG reconstruction needs sample support for sample-rootward traces. The existing iff theorem correctly exposes this missing hypothesis; it must stay explicit.",
    "G04": "The supplied coordinate-wise retention is not the Fig.5c global criterion of never coalescing anywhere. It is relevant to the final local unary removal stage and cannot close G04 alone.",
}

def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def git_bytes(path: str) -> bytes:
    return subprocess.run(["git", "show", f"{BASE}:{path}"], cwd=REPO, check=True, capture_output=True).stdout

def git_text(path: str) -> str:
    return git_bytes(path).decode("utf-8-sig")

def decl_line(content: str, full_name: str) -> int:
    suffix = full_name.split(".")[-1]
    # Namespace qualifications can occur in declarations themselves.
    pattern = re.compile(r"\b(?:theorem|lemma|def|abbrev|structure|inductive|instance)\s+(?:[\w.]+\.)?" + re.escape(suffix) + r"\b")
    for i, line in enumerate(content.splitlines(), 1):
        if pattern.search(line):
            return i
    raise AssertionError(f"Declaration not located: {full_name}")

def module_path(name: str) -> str:
    stem = name.split(".")[0]
    if stem in {"HistoryProjection", "AncestralRestriction", "AncestryContraction"}:
        return f"lean/SamuelAlexanderResearch/{stem}.lean"
    return f"real/{stem}.lean"

def text_content(node: ET.Element) -> str:
    return "".join(node.itertext())

def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-xml", type=Path, default=DEFAULT_XML)
    args = parser.parse_args()
    original = args.source_xml.read_bytes()
    assert sha(original) == XML_SHA256, "Primary XML bytes do not match the admitted input."
    xml = ET.fromstring(original)
    sections = {e.attrib["id"]: e for e in xml.findall("./body/sec") if "id" in e.attrib}
    ledger_path = "research/wong/completion/coverage.json"
    coverage = json.loads(git_text(ledger_path))
    ids = [c["id"] for c in coverage["claims"]]
    assert len(ids) == len(set(ids)) == 52
    assert set(ids) == set(PARAS) == set(ANCHORS)

    real_audit = git_text("real/RealAudit.lean")
    formal_audit = git_text("verification/FormalAudit.lean")
    selected_real = set(re.findall(r"^#print axioms (\S+)", real_audit, re.M))
    selected_core = set(re.findall(r"^#print axioms (\S+)", formal_audit, re.M))
    real_imports = set(re.findall(r"^import (\S+)", real_audit, re.M))
    lake = git_text("real/lakefile.lean")
    target_modules = set(re.findall(r"^lean_lib (\S+)", lake, re.M))
    module_cache: dict[str, str] = {}
    module_meta: dict[str, dict] = {}
    claims = []

    for claim in coverage["claims"]:
        cid = claim["id"]
        locators = []
        for section_id, paragraph_numbers in PARAS[cid]:
            paragraphs = sections[section_id].findall("./p")
            for p in paragraph_numbers:
                node = paragraphs[p - 1]
                locators.append({
                    "xpath": f'//sec[@id="{section_id}"]/p[{p}]',
                    "section_id": section_id,
                    "paragraph": p,
                    "text_sha256_utf8": sha(text_content(node).encode()),
                    "mathml_ids": [e.attrib["id"] for e in node.iter() if e.tag.endswith("}math") and "id" in e.attrib],
                })
        anchors = []
        for name in ANCHORS[cid]:
            path = module_path(name)
            if path not in module_cache:
                raw = git_bytes(path)
                module_cache[path] = raw.decode("utf-8-sig")
                stem = Path(path).stem
                module_meta[path] = {
                    "git_blob_sha256": sha(raw),
                    "base_commit": BASE,
                    "direct_real_audit_import": stem in real_imports,
                    "real_default_target": stem in target_modules,
                    "imports": re.findall(r"^import (\S+)", module_cache[path], re.M),
                    "note": "Core modules may be reached transitively; direct_real_audit_import=false is not an unimported claim.",
                }
            line = decl_line(module_cache[path], name)
            anchors.append({
                "declaration": name,
                "path": path,
                "line": line,
                "exact_base_link": f"{REPO_URL}/blob/{BASE}/{path}#L{line}",
                "declaration_presence": "lexical source check; not a new Lean run",
                "selected_in_real_audit": name in selected_real,
                "selected_in_core_audit": name in selected_core,
            })
        status = claim["status"]
        role = ("scoped checked evidence" if status == "checked scoped result" else
                "partial evidence; full target remains open" if status == "partial" else
                "prerequisite or related result only" if anchors else "no target declaration registered")
        claims.append({
            "id": cid,
            "title": claim["title"],
            "source_claim": claim["source_claim"],
            "source_url": claim["source_url"],
            "journal_pages": claim["journal_pages"],
            "pdf_pages_1based": claim["pdf_pages_1based"],
            "source_locators": locators,
            "baseline_status": status,
            "review_status": status,
            "evidence_role": role,
            "anchors": anchors,
            "baseline_assumptions": claim["assumptions"],
            "remaining_obligation": claim["remaining_target"],
            "audit_qualification": DIFFERENCES.get(cid),
        })

    historical = json.loads(git_text("verification/real-audit.json"))
    publication_path = "research/wong/completion/probability/holding-times/PUBLICATION.json"
    publication = json.loads(git_text(publication_path))
    frozen_matches = []
    for frozen in publication["frozen_dependencies"] + [{"path": "real/WongWaitingTimes.lean", "sha256": publication["source_sha256"]}]:
        observed = sha(git_bytes(frozen["path"]))
        assert observed == frozen["sha256"], f"Publication frozen-input mismatch: {frozen['path']}"
        frozen_matches.append({"path": frozen["path"], "sha256": observed, "matches_publication": True})
    selected_wong_inventory = []
    for name in sorted(selected_real):
        if not name.startswith("Wong"):
            continue
        path = module_path(name)
        if path not in module_cache:
            module_cache[path] = git_text(path)
        content = module_cache[path]
        if path not in module_meta:
            stem = Path(path).stem
            module_meta[path] = {
                "git_blob_sha256": sha(git_bytes(path)),
                "base_commit": BASE,
                "direct_real_audit_import": stem in real_imports,
                "real_default_target": stem in target_modules,
                "imports": re.findall(r"^import (\S+)", content, re.M),
                "note": "Additional selected Wong endpoint module; not every declaration claims a direct paper counterpart.",
            }
        line = decl_line(content, name)
        selected_wong_inventory.append({
            "declaration": name, "path": path, "line": line,
            "exact_base_link": f"{REPO_URL}/blob/{BASE}/{path}#L{line}",
            "declaration_presence": "lexical source check; not a new Lean run",
        })
    selected_wong = sorted(n for n in selected_real if n.startswith("Wong"))
    counts = dict(Counter(c["baseline_status"] for c in claims))
    out = {
        "schema_version": 1,
        "audit_kind": "independent source, declaration, import, and receipt inventory; no compilation",
        "base_commit": BASE,
        "coverage_ledger": {"path": ledger_path, "git_blob_sha256": sha(git_bytes(ledger_path))},
        "source": {"doi": "10.1093/genetics/iyae100", "primary_xml_sha256": XML_SHA256,
                   "primary_xml_local_path": str(args.source_xml), "primary_pdf": PDF_URL,
                   "live_review": "Publisher PDF text retrieved through browser; exact preserved XML and MathML rechecked. PDF screenshot transport returned no visible images, so no visual-review claim.",
                   "page_convention": "Journal page j = zero-based PDF page j = one-based PDF page j+1."},
        "inventory": {"claim_families": len(claims), "baseline_status_counts": counts,
                      "real_selected_endpoints": len(selected_real), "wong_selected_endpoints": len(selected_wong),
                      "endpoint_counts_are_not_paper_coverage_percentages": True},
        "verification_evidence": {
            "historical_repository_receipt": {"path": "verification/real-audit.json", "endpoint_count": historical["endpoint_count"],
                                              "checked_at_utc": historical["checked_at_utc"],
                                              "qualification": "This is a historical 274-endpoint receipt, not a fresh audit of BASE."},
            "publication_record": {"path": publication_path, "proof_commit": publication["proof_commit"],
                                   "run": publication["hosted_admission"]["run"],
                                   "conclusion": publication["hosted_admission"]["conclusion"],
                                   "counts": publication["hosted_admission"]["counts"],
                                   "qualification": "Stored hosted-admission record inspected; source hashes match BASE. CI was not independently rerun or re-fetched by this source lane."},
            "frozen_probability_sources": frozen_matches,
            "all_selected_wong_declarations_located_at_base": True,
            "new_compiler_run": False,
        },
        "module_evidence": module_meta,
        "selected_wong_endpoints": selected_wong,
        "selected_wong_endpoint_inventory": selected_wong_inventory,
        "claims": claims,
    }
    (HERE / "baseline-claim-audit.json").write_text(json.dumps(out, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    lines = [
        "# Wong source-to-theorem inventory at the continuation base", "",
        f"Audited Git snapshot: `{BASE}`. All repository evidence below is read with `git show` from this commit, even when the working checkout differs.", "",
        "This is a source and statement inventory, not a new compiler result. The 52 claim families remain visible. A theorem selected by an audit is evidence for its stated hypotheses and conclusion, not a percentage of the article.", "",
        f"The base selects {len(selected_real)} real-library endpoints, of which {len(selected_wong)} have a Wong namespace. The stored `verification/real-audit.json` still describes the historical {historical['endpoint_count']}-endpoint checkpoint. The waiting-time publication record records hosted success at `{publication['proof_commit']}`; its four probability-module hashes match this base. A final combined construction needs a fresh exact-commit receipt.", "",
        "The source is the [published article](" + PDF_URL + "). Journal page j is one-based PDF page j+1. Original Europe PMC XML SHA-256: `" + XML_SHA256 + "`. Browser text and original MathML were checked; the screenshot tool returned no visible page image, so visual verification is not claimed.", "",
        "| ID | Source locator | Status at base | Actual declaration anchors or boundary |", "|---|---|---|---|",
    ]
    for claim in claims:
        loc = "; ".join(f"{s}/p[{','.join(map(str, ps))}]" for s, ps in PARAS[claim["id"]])
        source = f"[{loc}]({claim['source_url']})"
        anchors_text = "; ".join(f"[{a['declaration']}]({a['exact_base_link']})" for a in claim["anchors"])
        if not anchors_text:
            anchors_text = "No target theorem registered; " + claim["evidence_role"] + "."
        else:
            anchors_text += ". " + claim["evidence_role"] + "."
        if claim["audit_qualification"]:
            anchors_text += " **Qualification:** " + claim["audit_qualification"]
        lines.append(f"| {claim['id']} — {claim['title']} | {source} | {claim['baseline_status']} | {anchors_text} |")
    lines += ["", "All per-family assumptions, unchanged remaining obligations, declaration line numbers, import and target registration, and the source paragraph hashes are in [baseline-claim-audit.json](baseline-claim-audit.json). [APPENDIX-B-CONTRACT.md](APPENDIX-B-CONTRACT.md) specifies the marked process and the endpoint-collision control.", "",
              "To rebuild this inventory, run `python research/wong/continuation-2026-09-27/source-audit/audit_baseline.py --source-xml <preserved-XML-path>` from the checkout. This command reads immutable Git blobs, checks the source and frozen-module hashes, and rewrites only this audit directory. It does not invoke Lean or modify the main ledger.", ""]
    (HERE / "BASELINE-AUDIT.md").write_text("\n".join(lines), encoding="utf-8")
    print(json.dumps({"base_commit": BASE, "claims": len(claims), "status_counts": counts,
                      "real_selected": len(selected_real), "wong_selected": len(selected_wong),
                      "frozen_probability_hashes": "PASS", "compiler_run": False}, indent=2))


if __name__ == "__main__":
    main()
