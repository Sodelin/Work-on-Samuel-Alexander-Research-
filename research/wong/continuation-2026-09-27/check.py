"""Compile the requested local import closure with pinned Lean, one process at a time.

Uses only the pinned official package cache; every project dependency is rebuilt
from this checkout. No project object is borrowed from a previous proof run.
"""
from __future__ import annotations
import argparse, hashlib, json, os, pathlib, re, subprocess, sys, time
sys.stdout.reconfigure(encoding='utf-8')

ROOT = pathlib.Path(__file__).resolve().parents[3]
BUILD = ROOT / '.local-build' / 'wong-continuation'
LEAN = pathlib.Path(r'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe')
PACKAGES = pathlib.Path(r'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization\real\.lake\packages')
MATHLIB_REV = '0df444a360eaa60ab8c11dca51a86af692955474'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def unexpected_axioms(output):
    reports = re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output)
    found = {name.strip() for names in reports for name in names.split(',') if name.strip()}
    return sorted(found - {'propext', 'Classical.choice', 'Quot.sound'})

def accepted_output(output):
    return 'sorryAx' not in output and 'Lean.ofReduceBool' not in output and not unexpected_axioms(output)

def git(*args, cwd=ROOT):
    return subprocess.check_output(['git', '-c', f'safe.directory={cwd.as_posix()}', *args], cwd=cwd, text=True, stderr=subprocess.PIPE).strip()

def source(module):
    rel = pathlib.Path(*module.split('.')).with_suffix('.lean')
    for base in [ROOT / 'real', ROOT / 'lean']:
        p = base / rel
        if p.is_file():
            return p
    return None

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('modules', nargs='+')
    ap.add_argument('--force', action='store_true')
    ap.add_argument('--recheck-targets', action='store_true', help='Recompile requested audit targets while retaining verified dependency objects.')
    ap.add_argument('--require-clean', action='store_true', help='Require the entire checkout to remain at a clean exact commit.')
    args = ap.parse_args()
    initial_commit = git('rev-parse', 'HEAD')
    initial_status = git('status', '--short')
    if args.require_clean and initial_status:
        raise SystemExit('Exact-commit verification requires a clean checkout:\n' + initial_status)
    BUILD.mkdir(parents=True, exist_ok=True)
    mathlib = PACKAGES / 'mathlib'
    actual_rev = git('rev-parse', 'HEAD', cwd=mathlib)
    if actual_rev != MATHLIB_REV:
        raise SystemExit(f'Mathlib revision mismatch: {actual_rev}')
    if git('diff', '--name-only', 'HEAD', cwd=mathlib):
        raise SystemExit('Pinned Mathlib has tracked changes; inspect before compiling.')
    paths = [BUILD, LEAN.parent.parent / 'lib' / 'lean'] + sorted(p / '.lake' / 'build' / 'lib' / 'lean' for p in PACKAGES.iterdir() if p.is_dir() and (p / '.lake' / 'build' / 'lib' / 'lean').is_dir())
    env = dict(os.environ, LEAN_PATH=';'.join(map(str, paths)))
    version = subprocess.check_output([str(LEAN), '--version'], text=True).strip()
    if '4.33.1' not in version:
        raise SystemExit(version)
    order, seen, project_imports = [], set(), {}
    def visit(module):
        if module in seen:
            return
        seen.add(module)
        p = source(module)
        if p is None:
            raise RuntimeError(f'Unknown requested project module {module}')
        text = p.read_text(encoding='utf-8-sig')
        if re.search(r'^\s*(?:axiom\s|.*\b(?:sorry|admit)\s*(?:--.*)?$)', text, re.M):
            raise RuntimeError(f'Unproved declaration marker in {p}')
        project_imports[module] = []
        for dep in re.findall(r'^\s*(?:public\s+)?import\s+([\w.]+)', text, re.M):
            if source(dep):
                project_imports[module].append(dep)
                visit(dep)
            else:
                obj = pathlib.Path(*dep.split('.')).with_suffix('.olean')
                if not any((base / obj).is_file() for base in paths[1:]):
                    raise RuntimeError(f'Missing pinned package object {dep}')
        order.append(module)
    for module in args.modules:
        visit(module)
    source_snapshot = {module: sha(source(module)) for module in order}
    rows = []
    for module in order:
        p = source(module)
        obj = BUILD / pathlib.Path(*module.split('.')).with_suffix('.olean')
        log = BUILD / (module + '.log')
        cache = BUILD / (module + '.json')
        dependencies = {m: sha(BUILD / pathlib.Path(*m.split('.')).with_suffix('.olean')) for m in project_imports[module]}
        signature = {'source_sha256': sha(p), 'dependencies': dependencies, 'mathlib_revision': actual_rev, 'lean': version}
        cached = json.loads(cache.read_text()) if cache.is_file() else {}
        cached_signature = cached.get('signature', {})
        signature_matches = all(cached_signature.get(k) == v for k, v in signature.items() if k != 'dependencies') and all(cached_signature.get('dependencies', {}).get(k) == v for k, v in dependencies.items())
        if (not args.force and not (args.recheck_targets and module in args.modules)
                and obj.is_file() and signature_matches
                and cached.get('exit_code') == 0 and cached.get('object_sha256') == sha(obj)
                and log.is_file() and cached.get('log_sha256') == sha(log)
                and accepted_output(log.read_text(encoding='utf-8'))):
            cached['signature'] = signature
            cache.write_text(json.dumps(cached, indent=2)+'\n')
            rows.append(cached)
            print(f'REUSE {module}', flush=True)
            continue
        obj.parent.mkdir(parents=True, exist_ok=True)
        start = time.time()
        result = subprocess.run([str(LEAN), '-j1', '-M4096', '-o', str(obj), str(p)], cwd=ROOT, env=env, capture_output=True, text=True, encoding='utf-8', errors='replace')
        output = result.stdout + result.stderr
        if sha(p) != signature['source_sha256']:
            raise RuntimeError(f'Source changed while Lean was checking {module}; this run is not verification evidence.')
        log.write_text(output, encoding='utf-8')
        attempt_dir = BUILD / 'attempts'
        attempt_dir.mkdir(exist_ok=True)
        (attempt_dir / f'{module}-{time.time_ns()}.log').write_text(output, encoding='utf-8')
        row = {'module': module, 'source': str(p.relative_to(ROOT)), 'signature': signature, 'exit_code': result.returncode, 'seconds': round(time.time()-start, 3), 'log_sha256': sha(log), 'object_sha256': sha(obj) if result.returncode == 0 and obj.is_file() else None}
        cache.write_text(json.dumps(row, indent=2)+'\n')
        rows.append(row)
        print(f'{"PASS" if result.returncode == 0 else "FAIL"} {module} {row["seconds"]}s', flush=True)
        bad_axioms = unexpected_axioms(output)
        if result.returncode or not accepted_output(output):
            print(output[-14000:])
            if bad_axioms:
                print('Unexpected axioms:', bad_axioms)
            return 1
    final_commit = git('rev-parse', 'HEAD')
    final_status = git('status', '--short')
    if final_commit != initial_commit or any(sha(source(m)) != h for m, h in source_snapshot.items()):
        raise RuntimeError('Commit or an imported source changed during verification; rerun at the stable checkpoint.')
    if args.require_clean and final_status:
        raise RuntimeError('Checkout changed during exact-commit verification:\n' + final_status)
    receipt = {'proof_commit': final_commit, 'working_tree_status': final_status, 'exact_clean_commit': args.require_clean, 'lean': version, 'mathlib_revision': actual_rev, 'modules': rows, 'status': 'PASS', 'scope': 'Requested import closure only; source correspondence and full repository verification are separate.'}
    (BUILD / 'receipt.json').write_text(json.dumps(receipt, indent=2)+'\n')
    target_receipt = BUILD / ('receipt-' + '-'.join(args.modules) + '.json')
    target_receipt.write_text(json.dumps(receipt, indent=2)+'\n')
    print(f'PASS {len(rows)} project modules; receipt {BUILD / "receipt.json"}')
    return 0

if __name__ == '__main__':
    # All proof lanes in this checkout use this OS lock. Windows releases it
    # if a process exits unexpectedly; no stale-owner file can block research.
    import msvcrt
    BUILD.mkdir(parents=True, exist_ok=True)
    with (BUILD / 'compiler.lock').open('a+b') as lock:
        if lock.tell() == 0:
            lock.write(b'0')
            lock.flush()
        announced = False
        while True:
            try:
                lock.seek(0)
                msvcrt.locking(lock.fileno(), msvcrt.LK_NBLCK, 1)
                break
            except OSError:
                if not announced:
                    print('QUEUED: waiting for the single compiler slot.', flush=True)
                    announced = True
                time.sleep(0.5)
        try:
            result = main()
        finally:
            lock.seek(0)
            msvcrt.locking(lock.fileno(), msvcrt.LK_UNLCK, 1)
    sys.exit(result)
