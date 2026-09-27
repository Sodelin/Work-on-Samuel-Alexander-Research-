"""Verify saved finite-family evidence and its exact Git sources; does not run Lean.

For a new kernel check, run the documented PedigreeBlockAudit command instead.
This deliberately checks only this seven-module proof closure, not the ARG audit.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess

PACKET = pathlib.Path(__file__).resolve().parent
ROOT = PACKET.parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
MATHLIB = "0df444a360eaa60ab8c11dca51a86af692955474"


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def sha_bytes(value):
    return hashlib.sha256(value).hexdigest()


def sha(path):
    return sha_bytes(path.read_bytes())


def read_json(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))


def git_bytes(*args):
    return subprocess.check_output(
        ["git", "-c", f"safe.directory={ROOT.as_posix()}", *args], cwd=ROOT
    )


def main():
    result = read_json(PACKET / "verification/RESULT.json")
    manifest = read_json(PACKET / "declarations.json")
    receipt_path = PACKET / "verification/combined-receipt.json"
    receipt = read_json(receipt_path)
    proof = result["proof_commit"]
    require(re.fullmatch(r"[0-9a-f]{40}", proof), "invalid proof commit")
    require(result["status"] == "PASS_LOCAL_EXACT_COMMIT", "result did not pass")
    require(receipt["status"] == "PASS", "combined receipt did not pass")
    require(receipt["proof_commit"] == proof, "receipt commit mismatch")
    require(receipt["exact_clean_commit"] and not receipt["working_tree_status"],
            "receipt was not from a clean exact commit")
    require(sha(receipt_path) == result["combined_receipt_sha256"], "receipt hash")
    require(receipt["mathlib_revision"] == result["mathlib_revision"] == MATHLIB,
            "Mathlib revision mismatch")
    require(receipt["lean"] == result["lean"] and "4.33.1" in receipt["lean"],
            "Lean version mismatch")
    require(set(result["allowed_axioms"]) == ALLOWED, "allowed-axiom policy")
    declarations = manifest["selected_declarations"]
    require(len(declarations) == len(set(declarations)) == manifest["count"] == 31,
            "selected declaration inventory")
    require(result["selected_new_declarations"] == 31, "result declaration count")
    rows = {row["module"]: row for row in receipt["modules"]}
    require(len(rows) == len(receipt["modules"]) == 7, "module count or duplicates")
    require(set(rows) == set(manifest["modules"]), "module inventory")
    require(result["project_import_closure_modules"] == 7, "result module count")

    for name, row in rows.items():
        rel = row["source"].replace("\\", "/")
        require(rel == f"real/{name}.lean", f"source path: {name}")
        signature = row["signature"]
        require(row["exit_code"] == 0, f"compiler exit: {name}")
        require(signature["lean"] == receipt["lean"], f"Lean signature: {name}")
        require(signature["mathlib_revision"] == MATHLIB, f"Mathlib signature: {name}")
        require(sha(ROOT / rel) == signature["source_sha256"], f"working source: {name}")
        require(sha_bytes(git_bytes("show", f"{proof}:{rel}")) == signature["source_sha256"],
                f"committed source: {name}")
        for dependency, object_hash in signature["dependencies"].items():
            require(dependency in rows and rows[dependency]["object_sha256"] == object_hash,
                    f"dependency object: {name} -> {dependency}")
        log_path = PACKET / "verification/logs" / f"{name}.log"
        require(sha(log_path) == row["log_sha256"], f"compiler log: {name}")
        log = log_path.read_text(encoding="utf-8")
        require("sorryAx" not in log and "Lean.ofReduceBool" not in log,
                f"unapproved axiom in {name}")
        for names in re.findall(r"depends on axioms:\s*\[([^\]]*)\]", log):
            require({v.strip() for v in names.split(",") if v.strip()} <= ALLOWED,
                    f"unexpected axiom in {name}")

    audit = (ROOT / "real/PedigreeBlockAudit.lean").read_text(encoding="utf-8")
    printed = re.findall(r"^#print axioms (\S+)$", audit, re.M)
    require(printed == declarations, "audit and declaration manifest differ")
    audit_log = (PACKET / "verification/logs/PedigreeBlockAudit.log").read_text(encoding="utf-8")
    reports = {}
    for match in re.finditer(
        r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)",
        audit_log,
    ):
        name = match[1]
        require(name not in reports, f"duplicate audit report: {name}")
        reports[name] = [v.strip() for v in (match[2] or "").split(",") if v.strip()]
    require(set(reports) == set(declarations), "missing or extra audited declaration")
    require(reports == result["endpoint_axioms"], "saved endpoint axiom inventory")

    for rel, digest in result["artifacts_sha256"].items():
        require(sha(PACKET / rel) == digest, f"packet artifact: {rel}")
    require(sha(PACKET / "check_recovery.py") == read_json(PACKET / "FINITE-CONTROLS.json")["script_sha256"],
            "finite controls came from a different script")
    ledger = read_json(PACKET / "LEDGER.json")
    require(ledger["checked_proof_commit"] == proof, "ledger commit")
    require(sum(row["status"] == "FORMAL_SCOPED_PASS" for row in ledger["claims"]) == 7,
            "formal scope ledger changed")
    print(json.dumps({
        "status": "PASS_SAVED_EVIDENCE_INTEGRITY_NOT_A_NEW_LEAN_RUN",
        "proof_commit": proof,
        "modules": len(rows),
        "selected_declarations": len(reports),
        "artifacts": len(result["artifacts_sha256"]),
        "prior_arg_audit": "preserved; not rerun or combined with this closure",
    }, indent=2))


if __name__ == "__main__":
    main()
