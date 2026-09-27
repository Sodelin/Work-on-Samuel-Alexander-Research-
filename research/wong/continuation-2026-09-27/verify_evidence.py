"""Validate the exact-commit evidence packet; this does not rerun Lean.

For a compiler replay use check.py RealAudit --require-clean on the named
proof commit, or the repository's portable checks/audit_lean.py --real route.
The evidence commit may follow the proof commit without changing any proof.
"""
from __future__ import annotations

import hashlib
import json
import pathlib
import re
import subprocess

HERE = pathlib.Path(__file__).resolve().parent
ROOT = HERE.parents[2]
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def main() -> None:
    result = json.loads((HERE / 'verification/RESULT.json').read_text(encoding='utf-8'))
    receipt_path = HERE / 'verification/combined-receipt.json'
    receipt = json.loads(receipt_path.read_text(encoding='utf-8'))
    assert digest(receipt_path.read_bytes()) == result['combined_receipt_sha256']
    assert receipt['status'] == 'PASS' and receipt['exact_clean_commit']
    assert receipt['working_tree_status'] == ''
    assert receipt['proof_commit'] == result['proof_commit']
    assert receipt['mathlib_revision'] == '0df444a360eaa60ab8c11dca51a86af692955474'
    commit = result['proof_commit']
    for row in receipt['modules']:
        assert row['exit_code'] == 0
        source = pathlib.Path(row['source']).as_posix().replace('\\', '/')
        committed = subprocess.check_output(['git', 'show', f'{commit}:{source}'], cwd=ROOT)
        assert digest(committed) == row['signature']['source_sha256'], source
        assert digest((ROOT / source).read_bytes()) == row['signature']['source_sha256'], source
    log_path = HERE / 'verification/RealAudit.log'
    assert digest(log_path.read_bytes()) == result['audit_log_sha256']
    output = log_path.read_text(encoding='utf-8')
    names = re.findall(r'^#print axioms (\S+)$', (ROOT / 'real/RealAudit.lean').read_text(), re.M)
    assert len(names) == len(set(names)) == result['selected_real_declarations']
    found = {name: {a.strip() for a in axioms.split(',') if a.strip()}
             for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", output)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms", output):
        found[name] = set()
    assert set(names) <= set(found), sorted(set(names) - set(found))
    assert all(found[name] <= ALLOWED for name in names)
    coverage = json.loads((ROOT / 'research/wong/completion/coverage.json').read_text(encoding='utf-8'))
    assert len(coverage['claims']) == len({c['id'] for c in coverage['claims']}) == 52
    assert not result['whole_paper_complete'] and not result['new_hosted_verification']
    print(f"PASS evidence: commit {commit}; {len(receipt['modules'])} project modules; "
          f"{len(names)} selected declarations; 52 source families.")
    print('This checks committed source/log integrity, not a new Lean compiler run.')


if __name__ == '__main__':
    main()
