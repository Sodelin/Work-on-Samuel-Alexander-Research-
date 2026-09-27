"""Verify a fresh proof receipt against current sources, logs and reading links.

This checks evidence integrity. It does not replace Lean compilation.
"""
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    receipt = json.loads((HERE / "verification/PROOF-RECEIPT.json").read_text())
    assert receipt["status"] == "PASS", receipt["status"]
    assert receipt["fresh_project_rebuild"], "A development replay is not release evidence"
    assert receipt["verification_script_sha256"] == sha(HERE / "verify.py")
    assert not receipt["unexpected_axioms"] and not receipt["missing_axiom_reports"]
    assert not receipt.get("changed_sources")
    assert receipt["no_sorryAx"]
    for row in receipt["modules"]:
        assert row["source_sha256"] == sha(ROOT / row["source_path"]), row["source_path"]
        assert row["log_sha256"] == sha(HERE / "verification" / row["log"]), row["log"]
        assert row["compiler_exit_code"] == 0, row["module"]
    assert receipt["axiom_log_sha256"] == sha(HERE / "verification/axioms.txt")
    expected = set()
    for src in HERE.glob("*.lean"):
        text = src.read_text(encoding="utf-8")
        ns = re.search(r"^namespace\s+(\w+)", text, re.M)[1]
        expected.update(ns + "." + name for name in re.findall(
            r"^(?:@\[[^\n]*\]\s*)?theorem\s+(\w+)", text, re.M))
    assert expected == set(receipt["axiom_reports"]), "The theorem inventory changed"
    pages = [ROOT / "GENOMES-AND-PEDIGREES.md", *HERE.glob("*.md")]
    link_count = 0
    for page in pages:
        for url in re.findall(r"\[[^\]]*\]\(([^)]+)\)", page.read_text(encoding="utf-8")):
            if re.match(r"[a-z]+:", url) or url.startswith("#"):
                continue
            path = url.split("#", 1)[0]
            assert (page.parent / path).exists(), (page.name, url)
            link_count += 1
    print(json.dumps({"status": "PASS", "source_modules": len(receipt["modules"]),
                      "public_theorems": len(expected), "local_links": link_count}, indent=2))


if __name__ == "__main__":
    main()
