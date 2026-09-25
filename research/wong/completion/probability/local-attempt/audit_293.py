"""Bounded integration check: three fresh modules plus exact 293 audit.

The 61 reused modules are bound to their fresh 274 source/object receipt.
The compiler slot must be granted by the programme auditor before execution.
"""
from pathlib import Path
from datetime import datetime,timezone
import hashlib,json,os,re,subprocess,time
S=Path(__file__).resolve().parent
P=S/'publish';B=S/'baseline';OLD=S.parent/'audit-project'
CACHE=S/'.lake/build/lib/lean'
OWNER=Path('C:/Users/Owner/Documents/Codex/2026-09-24/alexander-formalization')
COMPILER=Path('C:/Users/Owner/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean.exe')
MATHLIB='0df444a360eaa60ab8c11dca51a86af692955474'
ALLOWED={'propext','Quot.sound','Classical.choice'}
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def readj(p):return json.loads(p.read_text(encoding='utf-8-sig'))
def writej(p,x):p.parent.mkdir(parents=True,exist_ok=True);p.write_text(json.dumps(x,indent=2)+'\n',encoding='utf-8',newline='\n')
def parse(text):
 found={}
 for n,ax in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",text):
  assert n not in found,n;found[n]=[a.strip() for a in ax.split(',') if a.strip()]
 for n in re.findall(r"'([^']+)' does not depend on any axioms",text):assert n not in found;found[n]=[]
 for n,ax in found.items():assert set(ax)<=ALLOWED,(n,ax)
 return found

def main():
 started=datetime.now(timezone.utc).isoformat()
 old=readj(B/'verification/real-audit.json')
 assert sha(B/'verification/real-audit.json')==sha(S.parent/'evidence/combined-real-audit.json')
 assert old['endpoint_count']==274 and old['local_rebuild_count']==61
 reused=[]
 for rel,digest in old['source_sha256'].items():assert sha(OLD/rel)==digest,rel
 for row in old['local_rebuilds']:
  artifact=OLD/'.lake/build/lib/lean'/(row['module'].replace('.','/')+'.olean')
  assert sha(artifact)==row['olean_sha256'],str(artifact)
  reused.append({'module':row['module'],'source_sha256':row['source_sha256'],'olean_sha256':row['olean_sha256']})
 packages=OWNER/'real/.lake/packages'
 git=['git','-c',f"safe.directory={(packages/'mathlib').as_posix()}",'-C',str(packages/'mathlib')]
 rev=subprocess.run(git+['rev-parse','HEAD'],capture_output=True,text=True,check=True).stdout.strip();assert rev==MATHLIB
 clean=subprocess.run(git+['status','--porcelain','--untracked-files=no'],capture_output=True,text=True,check=True).stdout.strip();assert not clean
 version=subprocess.run([str(COMPILER),'--version'],capture_output=True,text=True,check=True).stdout.strip();assert 'version 4.33.1,' in version
 assert sha(COMPILER)==old['compiler_sha256']
 paths=[CACHE,OLD/'.lake/build/lib/lean']+[p/'.lake/build/lib/lean' for p in sorted(packages.iterdir()) if p.is_dir()]
 env=os.environ.copy();env['LEAN_PATH']=';'.join(str(p) for p in paths)
 src=readj(S/'SOURCE-MANIFEST.json');modules=[];source_hashes=dict(old['source_sha256']);logs=S/'verification/logs';logs.mkdir(parents=True,exist_ok=True)
 for row in src['modules']:
  name=row['module'];f=P/'real'/(name+'.lean');assert sha(f)==row['source_sha256'];out=CACHE/(name+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
  before=time.monotonic();command=[str(COMPILER),f'--root={P / "real"}','-j1','-M4096','-o',str(out),str(f)]
  r=subprocess.run(command,cwd=P/'real',env=env,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=300)
  text=r.stdout+r.stderr;log=logs/(name+'.txt');log.write_text(text,encoding='utf-8',newline='\n')
  assert r.returncode==0,(name,r.returncode,str(log))
  assert 'sorryAx' not in text
  found=parse(text);assert set(found)==set(row['endpoints']),(name,set(found),row['endpoints'])
  record={'module':name,'source_sha256':sha(f),'olean_sha256':sha(out),'log_sha256':sha(log),'exit_code':r.returncode,'warnings':len(re.findall(r'\bwarning:',text)),'elapsed_seconds':round(time.monotonic()-before,3),'endpoints':row['endpoints'],'endpoint_axioms':found,'command':command}
  modules.append(record);source_hashes['real/'+name+'.lean']=sha(f)
  writej(S/'verification/build-progress.json',{'started_utc':started,'modules':modules})
  print(f"PASS {name}: {len(found)} reports, {record['warnings']} warnings, {record['elapsed_seconds']}s",flush=True)
 manifest=P/'real/RealAudit.lean';names=re.findall(r'^#print axioms (\S+)\s*$',manifest.read_text(encoding='utf-8'),re.M)
 assert len(names)==len(set(names))==293 and set(old['endpoint_axioms'])<=set(names)
 r=subprocess.run([str(COMPILER),f'--root={P / "real"}','-j1','-M4096',str(manifest)],cwd=P/'real',env=env,capture_output=True,text=True,encoding='utf-8',errors='replace',timeout=300)
 text=r.stdout+r.stderr;log=logs/'RealAudit.txt';log.write_text(text,encoding='utf-8',newline='\n');assert r.returncode==0,(r.returncode,str(log));assert 'sorryAx' not in text
 found=parse(text);assert set(found)==set(names),(set(names)-set(found),set(found)-set(names))
 for row in reused:
  artifact=OLD/'.lake/build/lib/lean'/(row['module'].replace('.','/')+'.olean');assert sha(artifact)==row['olean_sha256']
 for rel,digest in old['source_sha256'].items():assert sha(OLD/rel)==digest,rel
 for row in modules:assert sha(P/'real'/(row['module']+'.lean'))==row['source_sha256']
 for rel in ('real/lakefile.lean','real/RealAudit.lean'):source_hashes[rel]=sha(P/rel)
 report={'checked_at_utc':datetime.now(timezone.utc).isoformat(),'started_at_utc':started,'lean_version':version,'toolchain_pin':'leanprover/lean4:v4.33.1','endpoint_count':293,'endpoint_axioms':{n:found[n] for n in names},'source_sha256':source_hashes,'dependencies':{'mathlib':MATHLIB},'project':'real','scope':'Three new modules freshly compiled; all61 reused local source and object bindings verified against the fresh274 receipt; exact293 selected endpoint audit. Source/statement review and hosted CI are separate.','source_inventory_scope':'All historical core sources and imported real local closure, with updated library/audit configuration.','baseline_commit':'46aac52e214311fb2c2230b1b4fe37c42ef9e1a9','baseline_receipt_sha256':sha(B/'verification/real-audit.json'),'new_local_rebuilds':modules,'reused_local_module_count':61,'reused_local_modules':reused,'compiler_sha256':sha(COMPILER),'script_sha256':sha(Path(__file__)),'aggregate_exit_code':r.returncode,'aggregate_warnings':len(re.findall(r'\bwarning:',text)),'aggregate_log_sha256':sha(log),'execution':{'lean_path':[str(p) for p in paths],'compiler':str(COMPILER),'new_cache':str(CACHE)},'hosted_ci_status':'NOT_RUN_FOR_THIS_STAGED_RELEASE'}
 writej(S/'verification/real-audit-293.json',report);writej(P/'verification/real-audit.json',report)
 print('PASS: exact293 endpoints; new3 rebuilt, reused61 source/object bindings checked; standard axioms only.',flush=True)
if __name__=='__main__':main()