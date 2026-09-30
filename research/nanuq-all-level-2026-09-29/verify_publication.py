"""Verify snapshot hashes and optionally recompute portable finite certificates."""
from hashlib import sha256
from pathlib import Path
import argparse
import json
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
def read(path):
    return json.loads(path.read_text(encoding='utf-8-sig'))

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--recompute',action='store_true')
    args=parser.parse_args()
    inventory=read(HERE/'SOURCE-INVENTORY.json')
    prefix='research/nanuq-all-level-2026-09-29/'
    for record in inventory['records']:
        relative=record['repository_path']
        assert relative.startswith(prefix)
        content=(HERE/relative[len(prefix):]).read_bytes()
        assert len(content)==record['bytes']
        assert sha256(content).hexdigest()==record['sha256'],relative
    report={'status':'PASS_INVENTORY','files':len(inventory['records']),
            'full_all_level_lean_check_performed':False,'recomputed':False}
    if args.recompute:
        with tempfile.TemporaryDirectory(prefix='nanuq-publication-') as temp:
            work=Path(temp)/'check'
            shutil.copytree(HERE,work,ignore=shutil.ignore_patterns('source-development','__pycache__'))
            commands=[[sys.executable,'-B',name] for name in
                      ('all_level_screen.py','independent_all_level_check.py',
                       'parameter_domain.py','independent_support_check.py',
                       'nonplanar_support_counterexample.py')]
            commands.append(['node','sidechat_support_check.cjs'])
            runs=[]
            for command in commands:
                start=time.monotonic()
                run=subprocess.run(command,cwd=work,text=True,encoding='utf-8',capture_output=True)
                if run.returncode:
                    print(run.stdout);print(run.stderr,file=sys.stderr)
                    raise RuntimeError(f'Check failed: {command}')
                runs.append({'program':command[-1],'exit_code':run.returncode,
                             'seconds':round(time.monotonic()-start,3),
                             'stdout_sha256':sha256(run.stdout.encode()).hexdigest()})
                if command[0]=='node':
                    rows=[json.loads(line) for line in run.stdout.splitlines() if line.strip()]
                    assert len(rows)==4 and sum(r['treeCases'] for r in rows)==84076
                    assert sum(r['selectedTrees'] for r in rows)==2525210
                    assert all(r['negative']==r['supportMismatches']==r['boundaryFailures']==0 for r in rows)
            finite=read(work/'independent-all-level-check.json')
            assert finite['total_trees']==84076 and finite['total_anchor_coefficients']==24667
            assert finite['total_four_point_copy_quartets']==11848859
            assert len(read(work/'parameter-domain.json')['inequalities'])==16
            assert read(work/'nonplanar-support-counterexample.json')['status']=='PASS'
            report.update(status='PASS_INVENTORY_AND_PORTABLE_FINITE_CHECKS',recomputed=True,runs=runs)
    print(json.dumps(report,indent=2))

if __name__=='__main__':
    main()
