"""Validate source-hashed proof evidence and the public reading route.

This checks artifact integrity, not biological correctness or theorem novelty.
Run after verify.py (without --development) and check_examples.py.
"""
from pathlib import Path
import hashlib
import json
import re
import subprocess
from urllib.parse import unquote

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    receipt = json.loads((HERE / "verification/PROOF-RECEIPT.json").read_text(encoding="utf-8"))
    assert receipt["status"] == "PASS" and receipt["fresh_project_rebuild"]
    assert receipt["no_sorryAx"] and not receipt["unexpected_axioms"]
    assert not receipt["missing_axiom_reports"]
    assert receipt["verification_script_sha256"] == sha(HERE / "verify.py")
    assert receipt["axiom_log_sha256"] == sha(HERE / "verification/axioms.txt")
    for module in receipt["modules"]:
        assert module["compiler_exit_code"] == 0
        assert module["source_sha256"] == sha(ROOT / module["source_path"]), module["module"]
        assert module["log_sha256"] == sha(HERE / "verification" / module["log"]), module["module"]
    examples = json.loads((HERE / "verification/EXACT-EXAMPLES.json").read_text(encoding="utf-8"))
    assert examples["status"] == "PASS"
    assert examples["script_sha256"] == sha(HERE / "check_examples.py")
    ledger = json.loads((HERE.parent / "problem-ledger.json").read_text(encoding="utf-8"))
    assert ledger["status_summary"]["author_questions_fully_solved"] == 0
    assert len(ledger["questions"]) == 12
    assert all(q["author_question_status"] == "open" for q in ledger["questions"])
    md = [ROOT / "TIME-AND-MEMORY.md", ROOT / "README.md",
          HERE.parent / "README.md", HERE.parent / "PROOF-STRUCTURE.md"] + sorted(HERE.glob("*.md"))
    links = 0
    for page in md:
        for target in re.findall(r"\]\(([^)]+)\)", page.read_text(encoding="utf-8")):
            if re.match(r"[a-zA-Z][\w+.-]*:", target) or target.startswith("#"):
                continue
            target = unquote(target.split("#")[0])
            assert (page.parent / target).exists(), f"Broken link: {page.name}: {target}"
            links += 1
    # A final source commit must contain the exact compiler inputs. This also
    # catches accidental line-ending normalization of a hash-pinned source.
    for module in receipt["modules"]:
        blob = subprocess.check_output(["git", "show", "HEAD:" + module["source_path"]], cwd=ROOT)
        assert hashlib.sha256(blob).hexdigest() == module["source_sha256"], module["source_path"]
    print(json.dumps({"status": "PASS", "project_sources": len(receipt["modules"]),
                      "new_theorems_audited": receipt["selected_new_theorem_count"],
                      "historical_endpoints_audited": receipt["selected_historical_endpoint_count"],
                      "markdown_files": len(md), "existing_local_links": links,
                      "full_author_questions_solved": 0}, indent=2))


if __name__ == "__main__":
    main()
