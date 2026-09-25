#!/usr/bin/env python3
"""Read-only verification of this immutable source and evidence packet."""
import hashlib, json, re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()
def read_json(name):
    return json.loads((ROOT / name).read_text(encoding="utf-8-sig"))
def text(path):
    data = path.read_bytes()
    return data.decode("utf-16" if data.startswith((b"\xff\xfe", b"\xfe\xff")) else "utf-8-sig")

manifest = read_json("MANIFEST.json")
assert manifest["selectedNewEndpointCount"] == 36
listed = {f["path"] for f in manifest["files"]}
assert len(listed) == len(manifest["files"])
assert "MANIFEST.json" not in listed
for f in manifest["files"]:
    p = ROOT / f["path"]
    assert p.resolve().is_relative_to(ROOT), f["path"]
    assert p.is_file() and p.stat().st_size == f["bytes"], f["path"]
    assert sha(p) == f["sha256"], f["path"]
actual = {str(p.relative_to(ROOT)).replace("\\", "/") for p in ROOT.rglob("*")
          if p.is_file() and not set(p.relative_to(ROOT).parts) & {".lake", ".replay", "__pycache__", ".git"}}
assert actual == listed | {"MANIFEST.json"}, (actual - listed - {"MANIFEST.json"}, listed - actual)
receipt = read_json("COMBINED-RECEIPT.json")
assert receipt["status"] == "LOCAL_NEW_MODULE_CHECKS_PASS"
assert receipt["freshCompleteDependencyReplay"] is False
assert len(receipt["modules"]) == 4
names = []
for m in receipt["modules"]:
    assert m["compilerExitCode"] == 0
    source = ROOT / m["source"]
    log = ROOT / m["log"]
    assert sha(source) == m["sourceSha256"]
    assert sha(log) == m["logSha256"]
    source_text, log_text = text(source), text(log)
    assert not re.search(r"(?m)^\s*(axiom|constant)\s|\bsorry\b|\badmit\b|\bnative_decide\b", source_text)
    assert not re.search(r"\bsorryAx\b|\bnative_decide\b|\berror:", log_text)
    reports = {n: {a.strip() for a in axes.split(",") if a.strip()}
               for n, axes in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log_text)}
    reports.update({n: set() for n in re.findall(r"'([^']+)' does not depend on any axioms", log_text)})
    expected = re.findall(r"(?m)^\s*#print axioms\s+(\S+)", source_text)
    assert set(expected) == set(reports) == set(m["selectedEndpoints"]), m["module"]
    assert all(axes <= ALLOWED for axes in reports.values())
    names += expected
assert len(names) == len(set(names)) == 36
dep = read_json("DEPENDENCIES.json")
assert dep["mathlibCommit"] == "0df444a360eaa60ab8c11dca51a86af692955474"
assert len(dep["localSourceOrder"]) == 13
available = set(dep["localSourceOrder"])
for module in available:
    src = ROOT / (module.replace(".", "/") + ".lean")
    assert src.is_file()
    for imp in re.findall(r"(?m)^import\s+(\S+)", text(src)):
        assert imp in available or imp == "Std" or imp.startswith(("Mathlib.", "Lean", "Batteries", "Init")), (module, imp)
links = 0
for name in listed:
    if name.endswith(".md"):
        for target in re.findall(r"(?<!!)\[[^\]]*\]\(([^)]+)\)", text(ROOT / name)):
            target = target.split("#", 1)[0]
            if not target or re.match(r"[A-Za-z]+://", target):
                continue
            assert (ROOT / name).parent.joinpath(target).is_file(), (name, target)
            links += 1
print(json.dumps({"status": "PACKET_INTEGRITY_PASS", "files": len(actual),
                  "customSourceModules": 13, "selectedNewEndpoints": 36,
                  "relativeMarkdownLinks": links, "leanInvoked": False}))
