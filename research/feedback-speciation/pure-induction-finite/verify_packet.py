#!/usr/bin/env python3
"""Integrity and saved-evidence check only. Never launches Lean or downloads."""
from pathlib import Path
from urllib.parse import unquote
import hashlib,json,re

ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def read_json(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def need(ok,msg):
    if not ok: raise SystemExit("FAIL: "+msg)
def log_text(p):
    data=p.read_bytes()
    return data.decode("utf-16" if data.startswith((b"\xff\xfe",b"\xfe\xff")) else "utf-8-sig")
def axiom_reports(p,names):
    text=log_text(p)
    pairs=re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",text)
    need([n for n,_ in pairs]==names,"Unexpected selected declarations in "+str(p))
    allowed={"propext","Classical.choice","Quot.sound"}
    for n,axes in pairs:
        actual={a.strip() for a in axes.split(",") if a.strip()}
        need(actual<=allowed,"Unexpected axiom for "+n)
    need("sorryAx" not in text,"sorryAx in "+str(p))
    return len(pairs)

manifest=read_json(ROOT/"MANIFEST.json")
need(manifest["selectedNewEndpointCount"]==4,"Wrong finite checkpoint scope")
seen=set()
for entry in manifest["files"]:
    rel=entry["path"]
    need(rel not in seen,"Duplicate manifest entry "+rel)
    seen.add(rel)
    p=(ROOT/rel).resolve()
    need(p.is_relative_to(ROOT),"Manifest path leaves packet")
    need(p.is_file(),"Missing file "+rel)
    need(p.stat().st_size==entry["bytes"],"Length mismatch "+rel)
    need(sha(p)==entry["sha256"],"Hash mismatch "+rel)
actual={p.relative_to(ROOT).as_posix() for p in ROOT.rglob("*") if p.is_file() and not any(part in {".lake",".replay",".git","__pycache__"} for part in p.relative_to(ROOT).parts)}
need(actual==seen|{"MANIFEST.json"},"Unlisted or omitted packet files")
worker=read_json(ROOT/"verification/worker-receipt.json")
need(worker["compilerExitCode"]==0,"Worker compile not successful")
need(sha(ROOT/"PureInductionJoint.lean")==worker["sourceSha256"],"Source does not match worker receipt")
need(sha(ROOT/"verification/PureInductionJoint.log")==worker["logSha256"],"Log does not match worker receipt")
need(sha(ROOT/"provenance/Original-Check.ps1")==worker["checkScriptSha256"],"Original wrapper mismatch")
expected=["PureInductionJoint."+s for s in ("joint_total","designated_probability","ordinary_01_22_frozen_real","pulse_00_01_frozen_real")]
need(worker["selectedEndpoints"]==expected,"Wrong four selected endpoints")
new_count=axiom_reports(ROOT/"verification/PureInductionJoint.log",expected)
review=read_json(ROOT/"verification/independent-scope-audit.json")
need(review["sourceSha256"]==worker["sourceSha256"],"Independent review source mismatch")
need(review["workerReceiptSha256"]==sha(ROOT/"verification/worker-receipt.json"),"Independent review receipt mismatch")
need(review["selectedEndpoints"]==expected,"Independent review endpoint mismatch")
dep_receipt=read_json(ROOT/"verification/finite-dependency-receipt.json")
dependency_count=0
for m in dep_receipt["modules"]:
    need(sha(ROOT/(m["module"]+".lean"))==m["sourceSha256"],"Dependency source mismatch")
    need(sha(ROOT/m["log"])==m["logSha256"],"Dependency log mismatch")
    dependency_count+=axiom_reports(ROOT/m["log"],m["selectedEndpoints"])
need(dependency_count==21,"Expected 21 inherited dependency reports")
deps=read_json(ROOT/"DEPENDENCIES.json")
lock=read_json(ROOT/"lake-manifest.json")
need(all(p["type"]=="git" for p in lock["packages"]),"Unexpected path dependency")
need({p["name"]:p["rev"] for p in lock["packages"]}=={p["name"]:p["rev"] for p in deps["packages"]},"Lockfile pin mismatch")
need(deps["mathlibCommit"]=="0df444a360eaa60ab8c11dca51a86af692955474","Mathlib pin mismatch")
need((ROOT/"lean-toolchain").read_text().strip()=="leanprover/lean4:v4.33.1","Toolchain mismatch")
links=0
for md in ROOT.rglob("*.md"):
    if any(part in {".lake",".replay",".git"} for part in md.relative_to(ROOT).parts): continue
    for ref in re.findall(r"\[[^\]]*\]\(([^)]+)\)",md.read_text(encoding="utf-8-sig")):
        target=ref.strip().strip("<>")
        if re.match(r"^[A-Za-z][A-Za-z0-9+.-]*:",target) or target.startswith("#"): continue
        target=unquote(target.split("#",1)[0])
        if not target: continue
        p=(md.parent/target).resolve()
        need(p.is_relative_to(ROOT) and p.is_file(),"Broken local link: "+str(md)+" -> "+target)
        links+=1
print(json.dumps({"status":"PACKET_INTEGRITY_AND_SAVED_REPORTS_PASS","manifestSha256":sha(ROOT/"MANIFEST.json"),"manifestMembers":len(seen),"packetFilesIncludingManifest":len(actual),"selectedNewEndpoints":new_count,"inheritedDependencyEndpoints":dependency_count,"localMarkdownLinksChecked":links,"leanInvoked":False,"freshReplayPerformed":False},indent=2))
