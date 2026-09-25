"""Compile the selected standalone research proof artifacts and audit printed axioms.

Run after the existing core and real library builds. This command neither builds
nor downloads dependencies, and its endpoint totals are separate from library counts.
A successful receipt certifies these formal statements against the selected built
imports; source-paper fidelity and dependency builds are separate checks.
"""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
ARTIFACTS = {
    "research/open-questions/ordinal/OrdinalCertificates.lean": 4,
    "research/open-questions/ordinal/ReachableRankNecessity.lean": 6,
    "research/open-questions/ordinal/HistoryWellFounded.lean": 3,
    "research/open-questions/ordinal/OrdinalHistoryRank.lean": 3,
    "research/open-questions/ordinal/HistoryPruning.lean": 3,
    "research/open-questions/ordinal/HistoryConverse.lean": 2,
    "research/open-questions/ordinal/GenericCertificate.lean": 8,
    "research/open-questions/ordinal/GenericOrdinalCertificate.lean": 3,
    "research/open-questions/embedding/GenericUniversalAvoiders.lean": 10,
    "research/open-questions/species/FounderWindow.lean": 4,
    "research/open-questions/genomic-identifiability/positive/ThreeTaxonIdentifiability.lean": 6,
    "research/open-questions/genomic-identifiability/next/ThreeTaxonFiniteEvidence.lean": 8,
    "research/feedback-speciation/package/AncestryMixing.lean": 10,
    "research/feedback-speciation/package/AncestryExamples.lean": 6,
    "research/feedback-speciation/package/FeedbackDynamics.lean": 19,
    "research/feedback-speciation/package/FogartyAffinity.lean": 9,
    "research/feedback-speciation/package/FogartyAffinityFixation.lean": 9,
    "research/open-problems/time-self-reference/exact-abstraction/ExactAbstraction.lean": 8,
    "research/open-problems/time-self-reference/exact-abstraction/MergeHistoryProjection.lean": 8,
    "research/feedback-speciation/finite-epigenetic/FiniteFixation.lean": 11,
    "research/feedback-speciation/finite-epigenetic/FiniteEpigenetic.lean": 10,
    "research/feedback-speciation/finite-epigenetic/DeterministicEpigenetic.lean": 10,
    "research/feedback-speciation/finite-epigenetic/RankingReversal.lean": 3,
    "research/feedback-speciation/pure-induction-finite/PureInductionJoint.lean": 4,
}
PRINT_NAMESPACES = {'research/open-problems/time-self-reference/exact-abstraction/ExactAbstraction.lean': 'ExactAbstraction.', 'research/open-problems/time-self-reference/exact-abstraction/MergeHistoryProjection.lean': 'MergeHistoryProjection.'}
PRINT_NAMESPACES.update({
    "research/feedback-speciation/finite-epigenetic/FiniteEpigenetic.lean": "FiniteEpigenetic.",
    "research/feedback-speciation/finite-epigenetic/RankingReversal.lean": "RankingReversal.",
})
PRINT_AXIOMS = re.compile(r"^\s*#print\s+axioms\s+([A-Za-z0-9_.]+)\s*$", re.M)
PLACEHOLDER_WARNING = re.compile(
    r"(?:warning[^\n]*(?:\bsorry\b|\badmit\b)|"
    r"declaration uses [^\n]*(?:\bsorry\b|\badmit\b)|\bsorryAx\b)",
    re.I,
)


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(command: list[str], cwd: Path, env: dict[str, str]) -> str:
    result = subprocess.run(
        command, cwd=cwd, env=env, text=True, encoding="utf-8",
        errors="replace", stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        check=False, timeout=300,
    )
    if result.returncode:
        raise RuntimeError(f"{command!r} exited {result.returncode}\n{result.stdout}")
    if PLACEHOLDER_WARNING.search(result.stdout):
        raise RuntimeError(f"Compiler reported a proof placeholder:\n{result.stdout}")
    return result.stdout


def read_pin(root: Path) -> tuple[str, dict[str, str]]:
    paths = [root / "lean-toolchain", root / "real" / "lean-toolchain"]
    pins = [p.read_text(encoding="utf-8").strip() for p in paths]
    if pins[0] != pins[1]:
        raise RuntimeError(f"Core and real toolchain pins disagree in {root}")
    if not re.fullmatch(r"leanprover/lean4:v[0-9]+\.[0-9]+\.[0-9]+", pins[0]):
        raise RuntimeError(f"Expected a release-pinned Lean toolchain, got {pins[0]!r}")
    return pins[0], {str(p): sha256(p) for p in paths}


def audit(source_root: Path, dependency_root: Path, compiler: Path | None) -> dict:
    source_root = source_root.resolve()
    dependency_root = dependency_root.resolve()
    project = dependency_root / "real"
    pin, pin_hashes = read_pin(dependency_root)
    source_pin_paths = [source_root / "lean-toolchain", source_root / "real" / "lean-toolchain"]
    if source_root != dependency_root and any(p.exists() for p in source_pin_paths):
        source_pin, source_pin_hashes = read_pin(source_root)
        if source_pin != pin:
            raise RuntimeError("Source and dependency checkouts have different Lean pins.")
        pin_hashes.update(source_pin_hashes)
    # A partial publication staging tree may omit project configuration. This is
    # allowed only with an explicit dependency root and is recorded in the receipt.
    pin_location = "source-and-dependency-root" if source_root == dependency_root else "dependency-root"
    if source_root != dependency_root and all(p.exists() for p in source_pin_paths):
        pin_location = "source-and-dependency-roots"

    env = os.environ.copy()
    env.pop("LEAN_PATH", None)
    cache_directory = dependency_root / ".lake/research-artifact-audit"
    cache_directory.mkdir(parents=True, exist_ok=True)
    search_paths: list[Path] = [cache_directory.resolve()]
    # Earlier selected artifacts may be imported by later ones. Keep their
    # generated oleans in this isolated cache, never next to the public sources.
    env["LEAN_PATH"] = str(cache_directory.resolve())
    if compiler is not None:
        compiler = compiler.resolve()
        if not compiler.is_file():
            raise RuntimeError(f"Explicit Lean compiler does not exist: {compiler}")
        search_paths += [
            dependency_root / "real/.lake/build/lib/lean",
            dependency_root / ".lake/build/lib/lean",
        ]
        packages = dependency_root / "real/.lake/packages"
        if packages.is_dir():
            search_paths.extend(sorted(packages.glob("*/.lake/build/lib/lean")))
        search_paths = [p.resolve() for p in search_paths if p.is_dir()]
        if len(search_paths) == 1:
            raise RuntimeError("No prebuilt dependency libraries were found.")
        env["LEAN_PATH"] = os.pathsep.join(str(p) for p in search_paths)
        prefix = [str(compiler)]
        mode = "explicit-compiler-with-process-local-cached-LEAN_PATH"
    else:
        prefix = ["lake", "env", "lean"]
        mode = "lake-env-lean-after-existing-library-builds"

    version = run(prefix + ["--version"], project, env).strip()
    expected_version = pin.split(":v", 1)[1]
    if not re.search(rf"\bversion {re.escape(expected_version)}(?:,|\s|$)", version):
        raise RuntimeError(f"Lean version differs from pin: {pin!r}, {version!r}")

    records = []
    all_names: set[str] = set()
    endpoint_axioms: dict[str, list[str]] = {}
    source_hashes = {}
    selected_modules = [Path(p).stem for p in ARTIFACTS]
    if len(selected_modules) != len(set(selected_modules)):
        raise RuntimeError("Selected research artifacts must have distinct module basenames.")
    for relative, expected_count in ARTIFACTS.items():
        path = source_root / relative
        before = sha256(path)
        text = path.read_text(encoding="utf-8")
        names = PRINT_AXIOMS.findall(text)
        namespace = PRINT_NAMESPACES.get(relative, "")
        names = [namespace + name for name in names]
        if len(names) != expected_count or len(names) != len(set(names)):
            raise RuntimeError(f"{relative}: expected {expected_count} unique printed endpoints, got {names!r}")
        if all_names.intersection(names):
            raise RuntimeError(f"Repeated endpoints across artifact files: {all_names.intersection(names)}")
        all_names.update(names)
        olean_path = cache_directory / f"{path.stem}.olean"
        command = prefix + [f"--root={path.parent}", "-o", str(olean_path), str(path)]
        output = run(command, project, env)
        found: dict[str, list[str]] = {}
        reports = re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)
        reports += [(n, "") for n in re.findall(r"'([^']+)' does not depend on any axioms", output)]
        for name, axioms in reports:
            if name in found:
                raise RuntimeError(f"Duplicate compiler axiom report for {name}")
            found[name] = [a.strip() for a in axioms.split(",") if a.strip()]
        if set(names) != set(found):
            raise RuntimeError(f"{relative}: compiler reports do not match declared endpoints; "
                               f"missing={sorted(set(names) - set(found))}, "
                               f"extra={sorted(set(found) - set(names))}\n{output}")
        unexpected = {n: sorted(set(found[n]) - ALLOWED_AXIOMS) for n in names}
        unexpected = {n: a for n, a in unexpected.items() if a}
        if unexpected:
            raise RuntimeError(f"Unapproved theorem axioms: {unexpected}")
        if sha256(path) != before:
            raise RuntimeError(f"Source changed during compilation: {relative}")
        source_hashes[relative] = before
        endpoint_axioms.update({name: found[name] for name in names})
        records.append({
            "path": relative, "source_sha256": before, "endpoint_count": len(names),
            "endpoints": names, "compiler_exit_code": 0,
            "generated_olean": str(olean_path), "generated_olean_sha256": sha256(olean_path),
            "compiler_output_sha256": hashlib.sha256(output.encode("utf-8")).hexdigest(),
            "compiler_output": output, "command": command,
        })
        print(f"PASS: {relative} ({len(names)} endpoints)", flush=True)
    # Detect edits to an earlier source while a later file was compiling.
    for relative, digest in source_hashes.items():
        if sha256(source_root / relative) != digest:
            raise RuntimeError(f"Source changed during the audit: {relative}")
    for name, digest in pin_hashes.items():
        if sha256(Path(name)) != digest:
            raise RuntimeError(f"Toolchain pin changed during the audit: {name}")
    return {
        "checked_at_utc": datetime.now(timezone.utc).isoformat(),
        "status": "PASS", "lean_version": version, "toolchain_pin": pin,
        "toolchain_pin_location": pin_location, "toolchain_pin_sha256": pin_hashes,
        "artifact_count": len(records), "endpoint_count": len(endpoint_axioms),
        "allowed_axioms": sorted(ALLOWED_AXIOMS), "endpoint_axioms": endpoint_axioms,
        "source_sha256": source_hashes, "artifacts": records,
        "execution": {
            "mode": mode, "source_root": str(source_root),
            "dependency_root": str(dependency_root), "working_directory": str(project),
            "compiler": str(compiler) if compiler else None,
            "process_local_lean_path": [str(p) for p in search_paths],
            "generated_artifact_cache": str(cache_directory),
            "compile_order": list(ARTIFACTS),
            "dependency_builds_performed": False,
            "dependency_downloads_requested": False,
        },
        "scope": f"{len(records)} selected standalone research artifacts; these {len(endpoint_axioms)} endpoints are separate from the registered core and real library totals. Statement review is separate.",
        "dependency_scope": "Compilation uses existing built imports. This audit does not rebuild or certify their source-to-object freshness; CI must run it after the existing core and real audits.",
        "auditor_sha256": sha256(Path(__file__)),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--source-root", type=Path, help="Explicit alternate source tree (recorded in receipt).")
    parser.add_argument("--dependency-root", type=Path, help="Explicit checkout containing prebuilt imports (recorded in receipt).")
    parser.add_argument("--compiler", type=Path, help="Exact installed Lean binary; use cached process-local LEAN_PATH instead of lake.")
    args = parser.parse_args()
    source_root = args.source_root or ROOT
    dependency_root = args.dependency_root or source_root
    report = audit(source_root, dependency_root, args.compiler)
    report["overrides"] = {
        "source_root": str(args.source_root.resolve()) if args.source_root else None,
        "dependency_root": str(args.dependency_root.resolve()) if args.dependency_root else None,
        "compiler": str(args.compiler.resolve()) if args.compiler else None,
    }
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(f"PASS: {report['endpoint_count']} standalone Lean endpoints; only permitted standard axioms.")
    print(report["lean_version"])


if __name__ == "__main__":
    main()
