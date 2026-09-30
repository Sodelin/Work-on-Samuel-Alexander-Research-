"""Record stable source inventory; do not promote cached artifacts to fresh proof."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
SNAPSHOT = HERE / 'checkpoints' / 'canonical-theta-20260929T233456Z'
EXCLUDED = {'GraphQuartetPortCounts', 'SourceProbe', 'ThetaProbe'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    frozen = json.loads((SNAPSHOT / 'manifest.json').read_text())
    sources = {p.stem: p for p in sorted(HERE.glob('*.lean'))}
    frozen_names = set(frozen['build_order'])
    mismatches = [name for name in frozen_names
                  if sha(sources[name]) != frozen['sha256']['src/' + name + '.lean']]
    assert not mismatches, mismatches
    dependencies = {}
    rows = []
    for name, path in sources.items():
        imports = []
        for line in path.read_text(encoding='utf-8-sig').splitlines():
            match = re.match(r'^import\s+(.+)$', line)
            if match:
                imports.extend(match.group(1).split())
        dependencies[name] = [dep for dep in imports if dep in sources]
        log, obj = path.with_suffix('.log'), path.with_suffix('.olean')
        log_text = log.read_text(encoding='utf-8-sig') if log.exists() else ''
        row = {
            'module': name, 'path': path.name, 'sha256': sha(path),
            'local_dependencies': dependencies[name],
            'external_imports': [dep for dep in imports if dep not in sources],
            'in_frozen_94_module_closure': name in frozen_names,
            'publication_class': ('excluded_failed_draft' if name == 'GraphQuartetPortCounts'
                else 'excluded_probe' if name in EXCLUDED else 'previously_compiled_source'),
            'cached_object_exists': obj.exists(),
            'cached_object_at_least_as_new_as_source': obj.exists() and obj.stat().st_mtime_ns >= path.stat().st_mtime_ns,
            'latest_log_contains_error_or_sorry': bool(re.search(r'\berror:|sorryAx|declaration uses `sorry`', log_text)),
        }
        if log.exists():
            row.update(log_path=log.name, log_sha256=sha(log))
        rows.append(row)
    order, active, done = [], set(), set()
    def visit(name):
        if name in done:
            return
        assert name not in EXCLUDED, 'Verified source imports excluded draft: ' + name
        assert name not in active, 'Import cycle: ' + name
        active.add(name)
        for dep in dependencies[name]:
            visit(dep)
        active.remove(name)
        done.add(name)
        order.append(name)
    for name in sources:
        if name not in EXCLUDED:
            visit(name)
    bad = [r['module'] for r in rows if r['module'] not in EXCLUDED and
           (not r['cached_object_at_least_as_new_as_source'] or r['latest_log_contains_error_or_sorry'])]
    assert not bad, bad
    builds = sorted(SNAPSHOT.glob('build-*'))
    latest = builds[-1] if builds else None
    completed = [name for name in frozen['build_order']
                 if latest and (latest / (name + '.olean')).exists() and (latest / (name + '.log')).exists()]
    receipt = SNAPSHOT / 'build-receipt.json'
    observed = datetime.now(timezone.utc).isoformat()
    status = json.loads(receipt.read_text()) if receipt.exists() else {
        'status': 'IN_PROGRESS', 'completed_modules_observed': len(completed),
        'expected_modules': len(frozen['build_order']),
        'next_module': next((n for n in frozen['build_order'] if n not in completed), None),
        'note': 'File observations plus live runner status; full PASS requires the final receipt.'}
    documentary = []
    for path in sorted(HERE.iterdir()):
        if path.is_file() and path.suffix in {'.md', '.json', '.py', '.ps1'} and not path.name.startswith('PUBLICATION-HANDOFF'):
            documentary.append({'path': path.name, 'sha256': sha(path)})
    manifest = {
        'observed_utc': observed, 'source_root': str(HERE),
        'source_editing_status': 'Stable; no proof edits planned during handoff. Background rebuild writes only into the checkpoint build directory.',
        'frozen_checkpoint': str(SNAPSHOT),
        'frozen_manifest_sha256': sha(SNAPSHOT / 'manifest.json'),
        'frozen_source_matches_working_source': True,
        'frozen_module_count': len(frozen_names),
        'all_source_module_count': len(rows), 'previously_compiled_module_count': len(order),
        'previously_compiled_build_order': order,
        'additional_modules_outside_frozen_closure': [n for n in order if n not in frozen_names],
        'excluded_modules': sorted(EXCLUDED),
        'compiler_version': frozen['compiler_version'],
        'compiler_sha256_on_original_host': frozen['compiler_sha256'],
        'mathlib_commit': frozen['mathlib_commit'],
        'fresh_checkpoint_rebuild_observation': status,
        'complete_raw_all_level_network_theorem_lean_checked': False,
        'new_all_level_support_audits_independently_reviewed_by_this_lane': False,
        'historical_compile_evidence_is_not_fresh_rebuild': True,
        'modules': rows, 'documentary_files': documentary,
    }
    (HERE / 'PUBLICATION-HANDOFF-MANIFEST.json').write_text(json.dumps(manifest, indent=2) + '\n', encoding='utf-8')
    additions = ', '.join('`' + name + '`' for name in manifest['additional_modules_outside_frozen_closure'])
    report = f'''# Stable formalization handoff

Observed {observed}. The proof sources are stable. Only the independent checkpoint rebuild is still producing output. No GitHub or website publication was performed by this handoff.

## Files to capture

Working source root: `{HERE}`.

Frozen canonical checkpoint: `checkpoints/canonical-theta-20260929T233456Z`.
Its immutable `manifest.json` lists 94 Lean modules and exact source hashes. All 94 still match the working source. `src/CanonicalTheta.lean` is the local theorem entry point; `src/VerifiedCheckpoint.lean` collects the audited dependencies.

`PUBLICATION-HANDOFF-MANIFEST.json` records all {len(rows)} current Lean sources, local imports, source/log hashes, exclusions, and a topological build order for the {len(order)} previously compiled modules. Cached objects and old logs are historical evidence, not a replacement for the fresh rebuild.

Capture `.lean`, `.md`, `.json`, `.py`, `.ps1`, relevant compiler `.log` files, and checkpoint source/context/manifests. Exclude `.olean`, `.ilean`, `.lake`, caches, and incomplete checkpoint directories. Keep failed/probe files in a clearly marked draft area or omit them from the verified build. Preserve dated manifests rather than overwriting them with newer claims.

## Completed formal endpoints

- `Nanuq.Canonical.theta_source`: arbitrary canonical theta arm counts (total at least one), original NANUQ circularity, pseudometric laws, strict separation, and exact support in the actual displayed edge splits.
- `Nanuq.Canonical.theta_weighted`: circularity, pseudometric laws, and exact displayed support for strictly positive rational terminal masses.
- `Nanuq.Canonical.theta_exact_quartet_mean`: the tensor is exactly the uniform mean over distinct displayed quartet resolutions. It is not a mean weighted by switching multiplicity.
- `RawNanuq`, `SourceFacts`, `SourceBlobFacts`: actual edge-indexed rooted binary DAG foundations, preserving parallel edges; switching trees, genuine displayed quartet resolutions, raw tensor symmetry/nonnegativity, source normalization, actual blob tree and port fibers. See each source for exact hypotheses.
- `GraphQuartetBridge`: a quartet with two branching blobs has a genuine original 2+2 bridge that forces its raw resolution.
- `GraphSwitchingChoices`: actual switching equivalence with hybrid incoming-edge choices, arbitrary subset extension, and subset/complement product equivalence.
- `Nanuq.AllLevelParameters.all_rows_iff_exact_domain`: the sixteen stated real inequalities are equivalent to `s=o=1`, `1/2 <= a <= 1`, `0 <= c <= a`. The same module proves the four-taxon inequality set is insufficient. This certifies the real algebra, not the external enumeration completeness.

Endpoint axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`. The finite theta certificates use kernel reduction. No new axiom, `sorry`, or native evaluation certificate is used for the completed endpoints.

## Additions outside the frozen dependency closure

{additions}.

These are separately compiled sources. Their dependencies and contemporaneous logs are in the manifest. They have not yet received one fresh combined rebuild with the frozen closure.

Excluded from the checked build: `GraphQuartetPortCounts` (known failed draft), `SourceProbe`, and `ThetaProbe` (scratch probes). `PORT-HELPERS-FROZEN.md` documents the failed wrapper. Its successful generic helper dependencies remain useful and are included.

## Exact remaining formal boundary

The complete raw-source all-level network theorem is NOT Lean checked. `AnchorComposition` proves aggregation conditional on the actual graph anchor identity. `CircularComposition` additionally needs local circularity and circular port preimages. The source graph representation/planarity and distinct-quartet preservation must still discharge those graph hypotheses. The canonical theta theorem alone does not prove classification of every raw blob.

The all-level computer-assisted argument, its representation and composition audits, and the new support audits belong to the adjacent research packet. This handoff does not independently recertify its recently reported support strengthening. Earlier dated scope notes remain historical and may predate that work.

The six-total-taxon structural bound remains established; minimality at six is not established. Five taxa already produce all sixteen inequality types in the external enumeration. The actual five-label witness in `FOUR-TAXON-OBSTRUCTION.json` rules out four total taxa for the full parameter-family criterion, not for every possible proof of original NANUQ. For positive cherry score `c`, the original multi-blob composition identity needs a correction; do not promote the local parameter theorem to a global family theorem unchanged.

## Fresh rebuild status

Observation: `{json.dumps({k:v for k,v in status.items() if k != 'results'})}`.

The runner compiles all 94 frozen local sources into a new object directory, without importing the working directory's objects. It reuses the pinned external Mathlib/dependency libraries. Only a final `build-receipt.json` with `status: PASS` and 94 checked modules certifies completion. The receipt was {'present' if receipt.exists() else 'not present'} at this observation.

## Reproduction

Pinned compiler: `{frozen['compiler_version']}`.
Pinned Mathlib commit: `{frozen['mathlib_commit']}`.

On the original Windows host, run from the frozen checkpoint:

```powershell
python rebuild.py --build .
```

The original-host script checks snapshot hashes, the compiler binary hash, the Mathlib commit, exit codes, and printed axiom dependencies. Its compiler/package locations come from the frozen manifest and are absolute. It is not advertised as a path-independent project.

For another host, preserve the frozen snapshot unchanged. Install the pinned Lean version, check out the pinned Mathlib revision with its locked dependencies, and build or fetch that version's dependency libraries. Use `rebuild_publication.py` from this directory with explicit locations; it validates source hashes, the Lean version/commit and Mathlib revision, and creates a fresh output directory. It records the actual host compiler hash instead of requiring the original Windows executable's hash.

```text
python rebuild_publication.py --source-dir FORMAL_FULL --lean LEAN_EXECUTABLE --packages MATHLIB_PROJECT/.lake/packages --mathlib MATHLIB_PROJECT --scope checkpoint --output NEW_BUILD_DIRECTORY
```

The `--packages` directory must contain the dependency package directories; `--mathlib` separately points to the pinned Mathlib checkout. `--scope all-checked` includes the separately compiled additions in dependency order and excludes the three draft/probe modules. A successful run writes `build-receipt.json`; this helper has not been claimed to have completed a fresh all-checked build during this handoff.

The Python five-label witness reproducer imports `all_level_screen.py` and `independent_all_level_check.py`, and reads `parameter-domain.json` and `independent-all-level-check.json` from the adjacent research packet. Copy those together and adjust its single `root` path to that packet on the reproduction host. It uses Python standard-library exact fractions.
'''
    (HERE / 'PUBLICATION-HANDOFF.md').write_text(report, encoding='utf-8')
    print(json.dumps({k: manifest[k] for k in ['observed_utc','all_source_module_count','previously_compiled_module_count','frozen_source_matches_working_source','additional_modules_outside_frozen_closure','fresh_checkpoint_rebuild_observation']}, indent=2))


if __name__ == '__main__':
    main()
