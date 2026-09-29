from pathlib import Path
import hashlib,json
r=Path(__file__).resolve().parent
m=json.loads((r/"MANIFEST.json").read_text(encoding="utf-8"))
for f in m["files"]:
 p=r/f["path"]
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=f["sha256"]:
  raise SystemExit("HASH FAILURE: "+f["path"])
print("PASS: "+str(len(m["files"]))+" manifest members match; this checks integrity, not a new Lean run.")
