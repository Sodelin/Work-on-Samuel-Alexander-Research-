from pathlib import Path
import hashlib,json,re,datetime
ROOT=Path(__file__).parent
EXPECTED={"FiniteFixation":("bcc30acb045721d4832c4a0da51ced7e825bc2ec0c7050e1d2a81327fb3676f9",11),
          "FiniteEpigenetic":("1a79a7a8ee8eca0950bbf97d17ae3e495a2c0268267041ee26b5be4b0031d822",10)}
ALLOWED={"propext","Classical.choice","Quot.sound"}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise RuntimeError(msg)
modules=[]
for stem,(expected,count) in EXPECTED.items():
 source=ROOT/(stem+".lean");log=ROOT/"verification"/(stem+".log");obj=ROOT/"build"/(stem+".olean")
 require(sha(source)==expected,"source changed after successful run: "+stem)
 text=log.read_text(encoding="utf-8-sig")
 require(": error:" not in text and "sorryAx" not in text,"build log failure "+stem)
 checks=re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]",text)
 require(len(checks)==count,"missing axiom endpoints "+stem)
 for endpoint,axioms in checks:
  used={x.strip() for x in axioms.split(",") if x.strip()}
  require(used<=ALLOWED,"unpermitted axiom: "+endpoint)
 require(obj.is_file() and obj.stat().st_size>0,"missing successful output "+stem)
 modules.append({"module":stem,"source":source.name,"sourceSha256":sha(source),
 "log":"verification/"+log.name,"logSha256":sha(log),"oleanSha256":sha(obj),
 "selectedEndpoints":[n for n,a in checks],"exitCode":0,
 "exitEvidence":"successful bounded command observed by root; no new compiler run by receipt writer"})
receipt={"schemaVersion":1,"status":"PASS","createdUtc":datetime.datetime.now(datetime.timezone.utc).isoformat(),
 "leanVersion":"4.33.1","leanCommit":"819816b2e0a3bf405af45ae5c7af2491d8f5bee6",
 "mathlibCommit":"0df444a360eaa60ab8c11dca51a86af692955474",
 "command":"lean.exe -j1 -M4096 -o build/<module>.olean <module>.lean",
 "allowedAxioms":sorted(ALLOWED),"selectedEndpointCount":sum(len(m["selectedEndpoints"]) for m in modules),
 "modules":modules,"boundaries":["formal model is the 81-state count specialization",
 "full phased-model correspondence independently audited by exact arithmetic, not a separate Lean reduction theorem",
 "deterministic comparison not covered by this receipt","no infinite path measure claimed",
 "no whole-paper or empirical species claim"]}
(ROOT/"verification"/"finite-receipt.json").write_text(json.dumps(receipt,indent=2)+"\n",encoding="utf-8")
print(json.dumps({"status":"PASS","selectedEndpointCount":receipt["selectedEndpointCount"],
 "receiptSha256":sha(ROOT/"verification"/"finite-receipt.json")}))
