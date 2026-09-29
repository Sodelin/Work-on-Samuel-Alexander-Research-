from pathlib import Path
import datetime, hashlib, json, re
ROOT=Path(__file__).resolve().parent
EXPECTED={
"FiniteFixation":("bcc30acb045721d4832c4a0da51ced7e825bc2ec0c7050e1d2a81327fb3676f9",11),
"FiniteEpigenetic":("1a79a7a8ee8eca0950bbf97d17ae3e495a2c0268267041ee26b5be4b0031d822",10),
"DeterministicEpigenetic":("ece655b0af42fbd580ca86b3f8176a8b4323fe3fd716da9429f13f6366f3117f",10),
"RankingReversal":("a1dcf86c7214e92ee8f319a46ea955c97c4d70aa83822a888573b41ad60a3894",3)}
ALLOWED={"propext","Classical.choice","Quot.sound"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
def main():
 prior_path=ROOT/"verification/finite-receipt.json"
 prior=json.loads(prior_path.read_text(encoding="utf-8"))
 old_modules={m["module"]:m for m in prior["modules"]}
 modules=[]
 for stem,(expected,count) in EXPECTED.items():
  source=ROOT/(stem+".lean");log=ROOT/"verification"/(stem+".log");obj=ROOT/"build"/(stem+".olean")
  require(sha(source)==expected,"Source changed since checked run: "+stem)
  output=log.read_text(encoding="utf-8-sig")
  require(not re.search(r"\berror:|sorryAx",output),"Failure in log: "+stem)
  checks=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",output)
  require(len(checks)==count and len({n for n,a in checks})==count,"Missing/duplicate endpoint: "+stem)
  for name,axioms in checks:
   require({a.strip() for a in axioms.split(",") if a.strip()}<=ALLOWED,"Unpermitted axiom: "+name)
  require(obj.is_file() and obj.stat().st_size>0,"Missing olean: "+stem)
  require(obj.stat().st_mtime>=source.stat().st_mtime,"Object older than source: "+stem)
  if stem in old_modules:
   old=old_modules[stem]
   require(old["sourceSha256"]==sha(source) and old["logSha256"]==sha(log) and old["oleanSha256"]==sha(obj),"Prior finite receipt differs: "+stem)
   exit_code=old["exitCode"];evidence="Terminal exit 0 observed in prior bounded check; frozen finite receipt agrees."
  elif stem=="RankingReversal":
   exit_code=0;evidence="Root observed terminal session 85365, chunk 5df71d, exit 0; imports all concrete models."
  else:
   exit_code=None;evidence="Original session 73786 was interrupted at the task layer and later returned Unknown process id. All 10 axiom reports and a fresh olean were emitted. RankingReversal subsequently imported this object and exited 0. The original process exit code was not retrieved."
  modules.append({"module":stem,"source":source.name,"sourceSha256":sha(source),"log":"verification/"+log.name,"logSha256":sha(log),"oleanSha256":sha(obj),"selectedEndpoints":[n for n,a in checks],"exitCode":exit_code,"exitEvidence":evidence})
 receipt={"schemaVersion":1,"status":"PASS_WITH_RECOVERED_EXIT_EVIDENCE","createdUtc":datetime.datetime.now(datetime.timezone.utc).isoformat(),"leanVersion":prior["leanVersion"],"leanCommit":prior["leanCommit"],"mathlibCommit":prior["mathlibCommit"],"command":prior["command"],"allowedAxioms":sorted(ALLOWED),"selectedEndpointCount":sum(len(m["selectedEndpoints"]) for m in modules),"modules":modules,"finiteReceiptSha256":sha(prior_path),"boundaries":["Selected endpoint count is not a paper completion percentage.","Finite limiting fixation probabilities and deterministic finite-tail ordering are checked.","Deterministic common-limit existence is not established by these four modules.","Full phased-life-cycle reductions are independently audited, not Lean transport theorems.","The finite model samples one diploid offspring per deme and permits selfing.","No empirical species, culture, whole-paper completion, or established novelty claim."]}
 target=ROOT/"verification/combined-receipt.json"
 target.write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8")
 print(json.dumps({"status":receipt["status"],"selectedEndpointCount":receipt["selectedEndpointCount"],"receiptSha256":sha(target)}))
if __name__=="__main__":main()
