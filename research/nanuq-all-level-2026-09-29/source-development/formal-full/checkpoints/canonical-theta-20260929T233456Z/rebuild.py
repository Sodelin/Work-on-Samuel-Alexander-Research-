"""Freeze a checked local theorem and rebuild its local dependency closure.

Only source and documentary files are copied. No working .olean file enters
the new build path. Existing pinned Mathlib/dependency libraries are reused.
The original working directory and the earlier frozen proof are not modified.
"""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
COMPILER = Path(r'C:\Users\Owner\.elan\toolchains\leanprover--lean4---v4.33.1\bin\lean.exe')
PACKAGES = Path(r'C:\Users\Owner\Documents\Codex\2026-09-24\alexander-formalization\real\.lake\packages')
EXPECTED_MATHLIB = '0df444a360eaa60ab8c11dca51a86af692955474'
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def local_closure(entry):
    order, active, done = [], set(), set()
    def visit(name):
        if name in done:
            return
        if name in active:
            raise RuntimeError(f'Import cycle: {name}')
        path = HERE / (name + '.lean')
        active.add(name)
        for line in path.read_text(encoding='utf-8-sig').splitlines():
            match = re.match(r'^import\s+(.+)$', line)
            if match:
                for dependency in match.group(1).split():
                    if (HERE / (dependency + '.lean')).exists():
                        visit(dependency)
        active.remove(name)
        done.add(name)
        order.append(name)
    visit(entry)
    return order


def freeze():
    order = local_closure('VerifiedCheckpoint')
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')
    target = HERE / 'checkpoints' / ('canonical-theta-' + stamp)
    target.mkdir(parents=True, exist_ok=False)
    source_dir = target / 'src'
    source_dir.mkdir()
    hashes = {}
    for name in order:
        source = HERE / (name + '.lean')
        copied = source_dir / source.name
        shutil.copyfile(source, copied)
        if sha(source) != sha(copied):
            raise RuntimeError(f'Source changed during snapshot: {name}')
        hashes['src/' + source.name] = sha(copied)
    docs = target / 'context'
    docs.mkdir()
    for name in ['OBLIGATIONS.md', 'SourceScope.md', 'SourceAnchorCompositionAudit.md',
                 'LOCAL-THEOREM-AUDIT.md', 'THETA-ASSEMBLY-REVIEW.md',
                 'anchor-composition-control.json']:
        source = HERE / name
        if source.exists():
            copied = docs / name
            shutil.copyfile(source, copied)
            hashes['context/' + name] = sha(copied)
    mathlib = subprocess.check_output(['git', '-c', 'safe.directory=' + (PACKAGES / 'mathlib').as_posix(), '-C', str(PACKAGES / 'mathlib'),
                                      'rev-parse', 'HEAD'], text=True).strip()
    if mathlib != EXPECTED_MATHLIB:
        raise RuntimeError(f'Mathlib pin differs: {mathlib}')
    version = subprocess.check_output([str(COMPILER), '--version'], text=True).strip()
    manifest = {
        'created_utc': stamp,
        'scope': 'Full unbounded canonical theta local theorem, raw graph foundations, and explicit conditional composition algebra',
        'full_raw_N2_source_theorem_complete': False,
        'external_peer_review': False,
        'global_priority_certified': False,
        'entrypoint': 'VerifiedCheckpoint',
        'build_order': order,
        'source_module_count': len(order),
        'compiler_path': str(COMPILER),
        'compiler_sha256': sha(COMPILER),
        'compiler_version': version,
        'mathlib_commit': mathlib,
        'packages_path': str(PACKAGES),
        'sha256': hashes,
        'fresh_local_build_status': 'PENDING; see build-receipt.json after rebuilding',
    }
    (target / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    shutil.copyfile(Path(__file__), target / 'rebuild.py')
    (target / 'README.md').write_text(
        '# Checked canonical theta theorem\n\n'
        'Entry point: `src/CanonicalTheta.lean`. Consolidated audit: '
        '`src/VerifiedCheckpoint.lean`. Read `context/OBLIGATIONS.md` for the '
        'boundary between the completed local theorem and the unfinished raw '
        'N2 graph theorem.\n\n'
        'Rebuild with the pinned compiler and installed dependency cache:\n\n'
        '```powershell\npython rebuild.py --build .\n```\n\n'
        'The rebuild compiles every included local source in dependency order. '
        'It uses a new build directory and does not import working-directory '
        'object files. It does reuse the existing pinned Mathlib dependency '
        'libraries. Its result is `build-receipt.json`; the manifest itself is '
        'an immutable source snapshot. No native-decide certificate or external '
        'Boolean result certifies a Lean theorem.\n', encoding='utf-8')
    print(str(target), flush=True)


def build(target):
    target = target.resolve()
    manifest = json.loads((target / 'manifest.json').read_text())
    for relative, digest in manifest['sha256'].items():
        if sha(target / relative) != digest:
            raise RuntimeError(f'Snapshot hash mismatch: {relative}')
    compiler = Path(manifest['compiler_path'])
    if sha(compiler) != manifest['compiler_sha256']:
        raise RuntimeError('Compiler hash differs from snapshot')
    packages = Path(manifest['packages_path'])
    mathlib = subprocess.check_output(['git', '-c', 'safe.directory=' + (packages / 'mathlib').as_posix(), '-C', str(packages / 'mathlib'),
                                      'rev-parse', 'HEAD'], text=True).strip()
    if mathlib != manifest['mathlib_commit']:
        raise RuntimeError('Mathlib pin differs from snapshot')
    build_dir = target / ('build-' + datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ'))
    build_dir.mkdir(exist_ok=False)
    paths = [build_dir]
    paths += [p / '.lake' / 'build' / 'lib' / 'lean' for p in sorted(packages.iterdir())
              if p.is_dir() and (p / '.lake' / 'build' / 'lib' / 'lean').exists()]
    env = os.environ.copy()
    env['LEAN_PATH'] = os.pathsep.join(map(str, paths))
    rows = []
    total_start = time.monotonic()
    status = 'PASS'
    for index, name in enumerate(manifest['build_order'], 1):
        print(f'[{index}/{len(manifest["build_order"])}] checking {name}', flush=True)
        start = time.monotonic()
        process = subprocess.run([str(compiler), '-o', str(build_dir / (name + '.olean')),
                                  str(target / 'src' / (name + '.lean'))],
                                 cwd=target / 'src', env=env, text=True, encoding='utf-8',
                                 errors='replace', stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        output = process.stdout
        log = build_dir / (name + '.log')
        log.write_text(output, encoding='utf-8')
        axioms = set()
        for group in re.findall(r'depends on axioms:\s*\[([^\]]*)\]', output, re.S):
            axioms.update(x.strip() for x in group.split(',') if x.strip())
        passed = process.returncode == 0 and not (axioms - ALLOWED_AXIOMS)
        passed = passed and 'sorryAx' not in output and 'declaration uses `sorry`' not in output
        row = {'module': name, 'exit_code': process.returncode, 'status': 'PASS' if passed else 'FAIL',
               'seconds': round(time.monotonic() - start, 3), 'axioms': sorted(axioms),
               'source_sha256': sha(target / 'src' / (name + '.lean')), 'log_sha256': sha(log)}
        if passed:
            row['olean_sha256'] = sha(build_dir / (name + '.olean'))
        rows.append(row)
        print(json.dumps(row), flush=True)
        if not passed:
            print(output, flush=True)
            status = 'FAIL'
            break
    receipt = {'status': status, 'fresh_local_sources': True,
               'reused_working_directory_oleans': False,
               'reused_pinned_external_dependency_libraries': True,
               'full_raw_N2_source_theorem_complete': False,
               'source_modules_checked': len(rows), 'expected_modules': len(manifest['build_order']),
               'seconds': round(time.monotonic() - total_start, 3),
               'build_directory': str(build_dir), 'results': rows}
    (target / 'build-receipt.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}), flush=True)
    if status != 'PASS':
        raise SystemExit(1)


if __name__ == '__main__':
    if len(sys.argv) == 3 and sys.argv[1] == '--build':
        build(Path(sys.argv[2]))
    elif len(sys.argv) == 1:
        freeze()
    else:
        raise SystemExit('Usage: checkpoint.py [--build SNAPSHOT_DIRECTORY]')
