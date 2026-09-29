"""Bounded benchmark of Lean's native incremental proof feedback.

Runs isolated copies under .lake, preserves raw diagnostics and actual exit
codes, and checks rejection of an intentionally false appended theorem.
This is development-tool evidence, never a substitute for the cold audit.
"""
from pathlib import Path
import json
import os
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def main():
    work = ROOT / ".lake" / "feedback-benchmark"
    work.mkdir(parents=True, exist_ok=True)
    source = ROOT / "lean/SamuelAlexanderResearch/GeneralRigidity.lean"
    probe = work / "FeedbackProbe.lean"
    snapshot = work / "feedback.snapshot"
    original = source.read_text(encoding="utf-8")
    probe.write_text(original, encoding="utf-8")
    lake = shutil.which("lake")
    if not lake:
        raise SystemExit("lake is not on PATH")
    results = []
    cases = [
        ("cold", [], original, 0),
        ("snapshot_save", [f"--incr-save={snapshot}"], original, 0),
        ("unchanged_reuse", [f"--incr-load={snapshot}"], original, 0),
        ("valid_append", [f"--incr-load={snapshot}"], original + "\nexample : 1 + 1 = 2 := rfl\n", 0),
        ("false_append", [f"--incr-load={snapshot}"], original + "\nexample : False := by decide\n", 1),
    ]
    for name, flags, contents, expected in cases:
        probe.write_text(contents, encoding="utf-8")
        start = time.perf_counter()
        proc = subprocess.run([lake, "env", "lean", *flags, str(probe)], cwd=ROOT,
                              env={**os.environ, "PYTHONIOENCODING": "utf-8"},
                              stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                              timeout=60, check=False)
        elapsed = time.perf_counter() - start
        log = work / f"{name}.log"
        log.write_bytes(proc.stdout)
        result = {"case": name, "seconds": round(elapsed, 3), "exit_code": proc.returncode,
                  "raw_bytes": len(proc.stdout), "log": str(log),
                  "expected_exit": expected, "passed": proc.returncode == expected}
        if proc.returncode != expected:
            result["diagnostics"] = proc.stdout.decode("utf-8", errors="replace")[-6000:]
        results.append(result)
        print(json.dumps(result), flush=True)
        if not result["passed"]:
            break
    probe.write_text(original, encoding="utf-8")
    report = {"source": str(source), "results": results,
              "all_expected": len(results) == len(cases) and all(r["passed"] for r in results)}
    (work / "result.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    return 0 if report["all_expected"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
