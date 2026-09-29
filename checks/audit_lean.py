"""Build the Lean library and audit its exported endpoints.

The source file verification/FormalAudit.lean is the endpoint manifest.
The audit rejects missing endpoints, unexpected axioms, and toolchain drift.
It records source hashes when --output is supplied. It does not certify that
the formal statements faithfully represent the source papers: that requires
the separate statement review documented in FORMALIZATION.md.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def run(command: list[str], cwd: Path = ROOT) -> str:
    result = subprocess.run(
        command, cwd=cwd, text=True, encoding="utf-8", errors="replace",
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False,
    )
    if result.returncode:
        raise RuntimeError(f"{command!r} exited {result.returncode}\n{result.stdout}")
    return result.stdout


def audit(real: bool = False) -> dict:
    project = ROOT / "real" if real else ROOT
    manifest = ROOT / "real" / "RealAudit.lean" if real else ROOT / "verification" / "FormalAudit.lean"
    names = re.findall(r"^#print axioms ([A-Za-z0-9_.]+)$", manifest.read_text(encoding="utf-8"), re.M)
    if not names or len(names) != len(set(names)):
        raise RuntimeError("The endpoint manifest must be nonempty and have unique names.")
    version = run(["lake", "env", "lean", "--version"], project).strip()
    pin = (project / "lean-toolchain").read_text(encoding="utf-8").strip()
    if ":v" not in pin or f"version {pin.split(':v', 1)[1]}," not in version:
        raise RuntimeError(f"Lean version differs from the repository pin: {pin!r}, {version!r}")
    # Refresh imports before checking their axioms or hashing their source files.
    # A caller must not receive a receipt for stale compiled dependencies.
    run(["lake", "build"], project)
    output = run(["lake", "env", "lean", str(manifest.relative_to(project))], project)
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output):
        found[name] = [a.strip() for a in axioms.split(",") if a.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        found[name] = []
    missing = sorted(set(names) - set(found))
    if missing:
        raise RuntimeError(f"Missing axiom reports: {missing}\n{output}")
    unexpected = {name: sorted(set(found[name]) - ALLOWED_AXIOMS) for name in names}
    unexpected = {name: axioms for name, axioms in unexpected.items() if axioms}
    if unexpected:
        raise RuntimeError(f"Unapproved theorem axioms: {unexpected}")
    paths = sorted((ROOT / "lean").rglob("*.lean")) + [manifest]
    dependencies = {}
    if real:
        expected_mathlib = "0df444a360eaa60ab8c11dca51a86af692955474"
        actual_mathlib = run(["git", "-C", ".lake/packages/mathlib", "rev-parse", "HEAD"], project).strip()
        if actual_mathlib != expected_mathlib:
            raise RuntimeError(f"Mathlib revision differs from the audited pin: {actual_mathlib}")
        if pin != (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip():
            raise RuntimeError("Real and core projects must use the same Lean version.")
        dependencies["mathlib"] = actual_mathlib
        # Inventory the local modules actually imported by this audit. Draft
        # files outside the imported graph are not certified source artifacts.
        pending = re.findall(r"^import (\S+)$", manifest.read_text(encoding="utf-8"), re.M)
        local_modules = set()
        while pending:
            module = pending.pop()
            source = project / (module.replace(".", "/") + ".lean")
            if source.is_file() and source not in local_modules:
                local_modules.add(source)
                pending.extend(re.findall(r"^import (\S+)$", source.read_text(encoding="utf-8"), re.M))
        paths += sorted(local_modules)
        paths += [project / "lakefile.lean", project / "lake-manifest.json", project / "lean-toolchain"]
    hashes = {p.relative_to(ROOT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
    return {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version,
        "toolchain_pin": pin,
        "endpoint_count": len(names),
        "endpoint_axioms": {name: found[name] for name in names},
        "source_sha256": hashes,
        "dependencies": dependencies,
        "project": "real" if real else "core",
        "scope": "Exported endpoint axiom audit; mathematical statement review is separate.",
        "source_inventory_scope": "All core Lean sources; the real audit additionally hashes its imported local module closure and project configuration, not unrelated draft files.",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--real", action="store_true", help="Audit the optional pinned Mathlib project.")
    args = parser.parse_args()
    report = audit(real=args.real)
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {report['endpoint_count']} Lean endpoints; only permitted standard axioms.")
    print(report["lean_version"])


if __name__ == "__main__":
    main()
