"""Replay the predictive-memory proofs with pinned, already installed Mathlib.

Usage: python verify.py --dependency-root /path/to/repo/real
All project imports are recompiled from this checkout in a fresh private folder.
Only external package oleans are reused. No shared lakefiles/cache are changed.
"""
from __future__ import annotations

import argparse
import atexit
import datetime as dt
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ALLOW = {"propext", "Classical.choice", "Quot.sound"}
PIN = "0df444a360eaa60ab8c11dca51a86af692955474"


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--dependency-root", type=Path, required=True)
    ap.add_argument("--lean", default="lean")
    ap.add_argument("--compiler-lock", type=Path,
                    help="Optional shared Windows byte-lock file; serialize this replay with other proof lanes")
    ap.add_argument("--development", action="store_true",
                    help="Reuse unchanged, previously checked private outputs; final receipt must use fresh replay")
    ap.add_argument("--modules", nargs="*", default=[
        "ControlledMemory", "HistoryObservation", "AncestryObservation", "WongPredictiveBridge"])
    args = ap.parse_args()
    if args.compiler_lock:
        if os.name != "nt":
            raise RuntimeError("--compiler-lock currently supports the coordinated Windows host only")
        import msvcrt
        handle = args.compiler_lock.open("a+b")
        print("Waiting for coordinated compiler slot...", flush=True)
        while True:
            try:
                handle.seek(0)
                msvcrt.locking(handle.fileno(), msvcrt.LK_NBLCK, 1)
                break
            except OSError:
                time.sleep(0.5)
        def release():
            handle.seek(0)
            msvcrt.locking(handle.fileno(), msvcrt.LK_UNLCK, 1)
            handle.close()
        atexit.register(release)
        print("Coordinated compiler slot acquired.", flush=True)
    packages = args.dependency_root.resolve() / ".lake" / "packages"
    mathlib = packages / "mathlib"
    rev = subprocess.check_output([
        "git", "-c", f"safe.directory={mathlib.as_posix()}", "-C", str(mathlib),
        "rev-parse", "HEAD"], text=True).strip()
    if rev != PIN:
        raise RuntimeError(f"Mathlib pin mismatch: {rev}")
    version = subprocess.check_output([args.lean, "--version"], text=True).strip()
    if "version 4.33.1," not in version:
        raise RuntimeError(f"Lean version mismatch: {version}")
    private = ROOT / ".lake" / "predictive-memory"
    private.mkdir(parents=True, exist_ok=True)
    build = (max(private.glob("replay-*"), key=lambda p: p.stat().st_mtime)
             if args.development and list(private.glob("replay-*"))
             else Path(tempfile.mkdtemp(prefix="replay-", dir=private)))
    logs = HERE / "verification"
    logs.mkdir(exist_ok=True)
    previous_path = logs / "PROOF-RECEIPT.json"
    previous = json.loads(previous_path.read_text(encoding="utf-8")) if previous_path.exists() else {}
    prior_modules = {m["module"]: m for m in previous.get("modules", [])}
    package_paths = sorted(p / ".lake/build/lib/lean" for p in packages.iterdir()
                           if (p / ".lake/build/lib/lean").is_dir())
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(map(str, [build] + package_paths)))

    roots = [HERE, HERE.parent / "exact-abstraction", ROOT / "real", ROOT / "lean"]
    inputs, order, visited = {}, [], set()

    def visit(name):
        if name in visited:
            return
        visited.add(name)
        relative = Path(*name.split(".")).with_suffix(".lean")
        found = next(((base, base / relative) for base in roots if (base / relative).is_file()), None)
        if found is None:
            # External imports must resolve to core or the pinned package cache.
            return
        base, src = found
        text = src.read_text(encoding="utf-8")
        for imported in re.findall(r"^import\s+([A-Za-z0-9_.]+)\s*$", text, re.M):
            visit(imported)
        inputs[name] = (base, src, relative)
        order.append(name)

    for name in ["MergeHistoryProjection"] + args.modules:
        visit(name)
    receipt = {
        "schema_version": "1.0", "status": "IN_PROGRESS",
        "checked_at_utc": dt.datetime.now(dt.timezone.utc).isoformat(),
        "compiler_version": version, "mathlib_commit": rev,
        "source_commit_before_replay": subprocess.check_output(
            ["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "source_identity_policy": "Per-file SHA256 below; commit may precede uncommitted input edits.",
        "standard_axiom_allowlist": sorted(ALLOW), "modules": [],
        "verification_script_sha256": sha(__file__),
        "fresh_project_rebuild": not args.development,
        "compiler_serialization": "shared OS byte lock" if args.compiler_lock else "caller managed",
    }
    receipt_path = logs / "PROOF-RECEIPT.json"

    def save():
        receipt_path.write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")

    endpoints = []
    invalidated = False
    for name in order:
        base, src, relative = inputs[name]
        output = build.joinpath(*name.split(".")).with_suffix(".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        old = prior_modules.get(name, {})
        reuse = (args.development and not invalidated and old.get("source_sha256") == sha(src)
                 and old.get("compiler_exit_code") == 0 and output.exists())
        if not reuse:
            invalidated = True
        proc = (subprocess.CompletedProcess([], 0, (logs / old["log"]).read_text(encoding="utf-8"))
                if reuse else subprocess.run([args.lean, "-o", str(output), str(relative)],
                              cwd=base, env=env, text=True, encoding="utf-8",
                              errors="replace", stdout=subprocess.PIPE,
                              stderr=subprocess.STDOUT, timeout=180))
        log_name = name.replace(".", "-") + ".txt"
        (logs / log_name).write_text(proc.stdout, encoding="utf-8")
        receipt["modules"].append({
            "module": name, "source_path": src.relative_to(ROOT).as_posix(),
            "source_sha256": sha(src), "compiler_exit_code": proc.returncode,
            "log": log_name, "log_sha256": sha(logs / log_name),
        })
        print(f"{name}: exit {proc.returncode}" + (" (development reuse)" if reuse else ""), flush=True)
        if proc.returncode or re.search(r"\bsorry\b|\bsorryAx\b", proc.stdout):
            receipt["status"] = "FAIL"
            save()
            print(proc.stdout)
            return 1
        # Audit every top-level theorem in the new modules, and the old selected endpoints.
        if src.parent == HERE:
            ns = re.search(r"^namespace\s+(\w+)", src.read_text(encoding="utf-8"), re.M)
            if ns:
                endpoints += [ns[1] + "." + t for t in re.findall(
                    r"^theorem\s+(\w+)", src.read_text(encoding="utf-8"), re.M)]
        else:
            # Historical selected reports are preserved verbatim in source. Also
            # audit their names in the final imported environment where fully qualified.
            pass
    historical = []
    for name in ["ExactAbstraction", "MergeHistoryProjection"]:
        historical += [name + "." + e for e in re.findall(r"^#print axioms (\S+)\s*$",
                                  inputs[name][1].read_text(encoding="utf-8"), re.M)]
    all_endpoints = endpoints + historical
    audit = build / "PredictiveMemoryAudit.lean"
    audit.write_text("\n".join([f"import {m}" for m in ["MergeHistoryProjection"] + args.modules] +
                               [f"#print axioms {e}" for e in all_endpoints]) + "\n", encoding="utf-8")
    proc = subprocess.run([args.lean, audit.name], cwd=build, env=env, text=True,
                          encoding="utf-8", errors="replace", stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=180)
    (logs / "axioms.txt").write_text(proc.stdout, encoding="utf-8")
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", proc.stdout)
    no_axioms = re.findall(r"'([^']+)' does not depend on any axioms", proc.stdout)
    checked = {n: [a.strip() for a in aa.replace("\n", " ").split(",") if a.strip()]
               for n, aa in reports}
    checked.update({n: [] for n in no_axioms})
    bad = {n: aa for n, aa in checked.items() if set(aa) - ALLOW}
    missing = sorted(set(all_endpoints) - set(checked))
    receipt.update({"axiom_audit_exit_code": proc.returncode,
                    "selected_new_theorem_count": len(endpoints),
                    "selected_historical_endpoint_count": len(historical),
                    "axiom_log_sha256": sha(logs / "axioms.txt"),
                    "axiom_reports": checked, "unexpected_axioms": bad,
                    "missing_axiom_reports": missing,
                    "no_sorryAx": not any("sorryAx" in aa for aa in checked.values()),
                    "status": "PASS" if proc.returncode == 0 and not bad and not missing else "FAIL"})
    save()
    print(f"{receipt['status']}: {len(checked)}/{len(all_endpoints)} axiom reports "
          f"({len(endpoints)} new, {len(historical)} historical)", flush=True)
    if receipt["status"] != "PASS":
        print(proc.stdout)
    return 0 if receipt["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
