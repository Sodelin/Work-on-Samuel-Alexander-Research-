from pathlib import Path
import hashlib, json, re, zipfile
root = Path(__file__).resolve().parent
names = [
"README.md","RESEARCH-CONTRACT.md","MANUSCRIPT.md","MANUSCRIPT.html",
"FOGARTY-GLOBAL-RATE.md","FOGARTY-GLOBAL-RATE.html","REVIEW-START.html",
"CLAIM-LEDGER.md","OPEN-PROBLEMS.md","PRIOR-WORK-AUDIT.md","RATE-PRIOR-ART-CHECK.md",
"REVIEW-NOTES.md","rate-statement-review.md","HANDOFFS.md","SOURCE-AUDIT.md",
"SOURCE-ORIGINS.md","VERIFICATION.md","WONG-REMAINING-WORK.md",
"build_review_archive.py","package/Check-All.ps1","package/lakefile.lean",
"package/lean-toolchain","package/lake-manifest.json",
"package/AncestryMixing.lean","package/AncestryExamples.lean","package/FeedbackDynamics.lean",
"package/FogartyAffinity.lean","package/FogartyAffinityFixation.lean",
"package/vendor/SamuelAlexanderResearch/SpeciesBridge.lean",
"package/vendor/SamuelAlexanderResearch/SpeciesGlobalIAP.lean"]
names += [p.relative_to(root).as_posix() for p in sorted((root/"package/verification").iterdir()) if p.is_file()]
assert len(names) == len(set(names))
for name in names:
    assert (root/name).is_file(), name
receipt = json.loads((root/"package/verification/receipt.json").read_text(encoding="utf-8-sig"))
assert receipt["status"] == "PASS" and len(receipt["modules"]) == 7
total = 0
for module in receipt["modules"]:
    source = root/"package"/module["path"]
    assert hashlib.sha256(source.read_bytes()).hexdigest().lower() == module["sha256"].lower()
    assert module["exitCode"] == 0
    for endpoint in module["selectedEndpoints"]:
        assert set(endpoint["axioms"]).issubset({"propext","Classical.choice","Quot.sound"})
        total += 1
assert total == 72
for name in names:
    if name.endswith(".md"):
        text = (root/name).read_text(encoding="utf-8-sig")
        for target in re.findall(r"\]\(([^)]+)\)", text):
            if "://" in target or target.startswith(("#","mailto:")): continue
            target = target.split("#")[0].split(" ")[0].strip("<>")
            if not target: continue
            assert (root/name).parent.joinpath(target).exists(), (name,target)
lines = [hashlib.sha256((root/name).read_bytes()).hexdigest()+"  "+name for name in sorted(names)]
(root/"SHA256SUMS.txt").write_text("\n".join(lines)+"\n",encoding="utf-8")
archive = root.parent/"feedback-speciation-review-2026-09-25.zip"
with zipfile.ZipFile(archive,"w",compression=zipfile.ZIP_DEFLATED,compresslevel=9) as z:
    for name in sorted(names+["SHA256SUMS.txt"]):
        z.write(root/name, "feedback-speciation/"+name)
with zipfile.ZipFile(archive) as z:
    assert z.testzip() is None
    for line in lines:
        expected,name=line.split("  ",1)
        assert hashlib.sha256(z.read("feedback-speciation/"+name)).hexdigest() == expected
digest=hashlib.sha256(archive.read_bytes()).hexdigest()
archive.with_suffix(".zip.sha256").write_text(digest+"  "+archive.name+"\n",encoding="utf-8")
print(json.dumps({"archive":str(archive),"sha256":digest,"bytes":archive.stat().st_size,
"files":len(names)+1,"modules":7,"selectedEndpoints":total,"sourceHashesMatchReceipt":True,
"localMarkdownLinksValid":True,"archiveHashesVerified":True},indent=2))
