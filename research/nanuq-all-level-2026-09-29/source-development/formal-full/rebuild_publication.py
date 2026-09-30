"""Path-configurable fresh rebuild of the stable publication source inventory."""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--source-dir', type=Path, required=True)
    parser.add_argument('--lean', type=Path, required=True)
    parser.add_argument('--packages', type=Path, required=True)
    parser.add_argument('--mathlib', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--scope', choices=['checkpoint', 'all-checked'], default='checkpoint')
    args = parser.parse_args()
    source, compiler = args.source_dir.resolve(), args.lean.resolve()
    packages, mathlib = args.packages.resolve(), args.mathlib.resolve()
    manifest_file = source / 'PUBLICATION-HANDOFF-MANIFEST.json'
    manifest = json.loads(manifest_file.read_text(encoding='utf-8'))
    rows = {r['module']: r for r in manifest['modules']}
    order = manifest['previously_compiled_build_order']
    if args.scope == 'checkpoint':
        order = [n for n in order if rows[n]['in_frozen_94_module_closure']]
        assert len(order) == manifest['frozen_module_count']
    assert not set(order).intersection(manifest['excluded_modules'])
    for name in order:
        assert sha(source / rows[name]['path']) == rows[name]['sha256'], 'Changed source: ' + name
        assert set(rows[name]['local_dependencies']) <= set(order), 'Missing dependency: ' + name
    version = subprocess.check_output([str(compiler), '--version'], text=True).strip()
    for pattern in [r'version\s+([\w.+-]+)', r'commit\s+([0-9a-f]+)']:
        expected = re.search(pattern, manifest['compiler_version'])
        actual = re.search(pattern, version)
        assert expected and actual and expected[1] == actual[1], 'Compiler version/commit mismatch'
    commit = subprocess.check_output(['git', '-c', 'safe.directory=' + mathlib.as_posix(),
        '-C', str(mathlib), 'rev-parse', 'HEAD'], text=True).strip()
    assert commit == manifest['mathlib_commit'], 'Mathlib revision mismatch'
    build = args.output.resolve()
    build.mkdir(parents=True, exist_ok=False)
    libraries = [mathlib / '.lake' / 'build' / 'lib' / 'lean']
    libraries += [p / '.lake' / 'build' / 'lib' / 'lean' for p in sorted(packages.iterdir())
                  if p.is_dir() and (p / '.lake' / 'build' / 'lib' / 'lean').is_dir()]
    assert libraries[0].is_dir(), 'Build/fetch the pinned Mathlib libraries first'
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(str(p) for p in dict.fromkeys([build] + libraries))
    results = []
    receipt = {
        'started_utc': datetime.now(timezone.utc).isoformat(), 'status': 'IN_PROGRESS',
        'scope': args.scope, 'expected_modules': len(order), 'results': results,
        'handoff_manifest_sha256': sha(manifest_file), 'compiler_version': version,
        'compiler_sha256': sha(compiler), 'mathlib_commit': commit,
        'reused_working_directory_oleans': False,
        'reused_pinned_external_dependency_libraries': True,
        'complete_raw_all_level_network_theorem_lean_checked': False,
    }
    def save():
        (build / 'build-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
    save()
    for index, name in enumerate(order, 1):
        print(f'[{index}/{len(order)}] checking {name}', flush=True)
        started = time.monotonic()
        process = subprocess.run([str(compiler), '-o', str(build / (name + '.olean')),
            str(source / rows[name]['path'])], cwd=source, env=env, text=True,
            encoding='utf-8', errors='replace', stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        log = build / (name + '.log')
        log.write_text(process.stdout, encoding='utf-8')
        axioms = set()
        for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', process.stdout, re.S):
            axioms.update(a.strip() for a in group.split(',') if a.strip())
        passed = (process.returncode == 0 and not axioms - {'propext', 'Classical.choice', 'Quot.sound'}
                  and 'sorryAx' not in process.stdout and 'declaration uses `sorry`' not in process.stdout)
        result = {'module': name, 'exit_code': process.returncode,
            'status': 'PASS' if passed else 'FAIL', 'axioms': sorted(axioms),
            'seconds': round(time.monotonic() - started, 3),
            'source_sha256': sha(source / rows[name]['path']), 'log_sha256': sha(log)}
        if passed:
            result['olean_sha256'] = sha(build / (name + '.olean'))
        results.append(result)
        print(json.dumps(result), flush=True)
        receipt['source_modules_checked'] = len(results)
        if not passed:
            receipt['status'] = 'FAIL'
            save()
            print(process.stdout, flush=True)
            raise SystemExit(1)
        save()
    receipt['status'] = 'PASS'
    receipt['completed_utc'] = datetime.now(timezone.utc).isoformat()
    save()
    print(json.dumps({k:v for k,v in receipt.items() if k != 'results'}), flush=True)


if __name__ == '__main__':
    main()
