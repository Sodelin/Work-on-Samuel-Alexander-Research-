"""Check the frozen bridge source/receipt/log correspondence; do not run Lean."""

from __future__ import annotations

import hashlib
import json
import pathlib
import re


HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EVIDENCE = HERE / "verification"
SOURCE = ROOT / "real" / "WongPedigreeBridge.lean"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def sha(path: pathlib.Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    row = json.loads((EVIDENCE / "WongPedigreeBridge.json").read_text())
    receipt = json.loads((EVIDENCE / "import-closure-receipt.json").read_text())
    log_path = EVIDENCE / "WongPedigreeBridge.log"
    log = log_path.read_text(encoding="utf-8")
    assert row["exit_code"] == 0
    assert receipt["status"] == "PASS"
    assert row["signature"]["source_sha256"] == sha(SOURCE)
    assert row["log_sha256"] == sha(log_path)
    assert "sorryAx" not in log and "Lean.ofReduceBool" not in log and "error:" not in log
    module_rows = {entry["module"]: entry for entry in receipt["modules"]}
    assert module_rows["WongPedigreeBridge"] == row
    for entry in module_rows.values():
        assert entry["exit_code"] == 0
        assert entry["signature"]["source_sha256"] == sha(ROOT / entry["source"])
    expected = re.findall(r"^#print axioms (\S+)$", SOURCE.read_text(encoding="utf-8"), re.M)
    found = {}
    pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
    for name, text in re.findall(pattern, log, flags=re.S):
        axioms = sorted(piece.strip() for piece in text.split(",") if piece.strip())
        assert set(axioms) <= ALLOWED, (name, axioms)
        found[name] = axioms
    assert set(found) == set(expected) and len(expected) == 14
    result = {
        "status": "PASS_SOURCE_SNAPSHOT_PENDING_INTEGRATED_COMMIT",
        "proof_base_commit": receipt["proof_commit"],
        "source_sha256": sha(SOURCE),
        "log_sha256": sha(log_path),
        "project_import_closure_modules": len(module_rows),
        "acceptance_endpoints": found,
        "lean": receipt["lean"],
        "mathlib_revision": receipt["mathlib_revision"],
        "scope": "Source snapshot and preserved compiler evidence. The final combined exact commit is verified by the parent lane.",
    }
    (EVIDENCE / "RESULT.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
