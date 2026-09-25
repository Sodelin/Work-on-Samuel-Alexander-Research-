"""Bounded checks of the declared toys; no Lean invocation or empirical claims."""
from __future__ import annotations
from collections import Counter
from datetime import datetime, timezone
from hashlib import sha256
from itertools import product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
B = (0, 1)
ACTIONS = ("wait", "prime", "probe", "reset")
BASE_ACTIONS = ("wait", "prime", "reset")
CELL = tuple(product(B, repeat=3))
MAX_HISTORY = 3
HORIZON = 4
HISTORIES = tuple(h for length in range(MAX_HISTORY + 1)
                  for h in product(B, repeat=length))
DECISION = tuple((v, h) for v in B for h in HISTORIES)

def parity(h):
    return sum(h) % 2

def cell_step(a, s):
    v, m, n = s
    return {
        "wait": (v, m, 1 - n),
        "prime": (v, 1 - m, 1 - n),
        "probe": (m, m, 1 - n),
        "reset": (0, 0, 1 - n),
    }[a]

def decision_step(a, s):
    v, h = s
    if a == "wait":
        return v, h + (0,)
    if a == "prime":
        return v, h + (1,)
    if a == "probe":
        return parity(h), h + (0,)
    if a == "reset":
        return 0, ()
    raise ValueError(a)

def abstract_step(a, z):
    v, m = z
    if a == "wait":
        return v, m
    if a == "prime":
        return v, 1 - m
    if a == "probe":
        return m, m
    if a == "reset":
        return 0, 0
    raise ValueError(a)

def qc(s):
    return s[0], s[1]

def qd(s):
    return s[0], parity(s[1])

def p(s):
    return s[0]

def first_collision(states, actions, step, observation):
    for a in actions:
        seen = {}
        for s in states:
            before, after = observation(s), observation(step(a, s))
            if before in seen and seen[before][1] != after:
                return {
                    "action": a,
                    "left_state": seen[before][0],
                    "right_state": s,
                    "shared_observation": before,
                    "left_next_observation": seen[before][1],
                    "right_next_observation": after,
                }
            seen[before] = (s, after)
    return None

commuting_counts = {}
for name, states, step, observe in (
    ("cell", CELL, cell_step, qc),
    ("decision_bounded_initial_histories", DECISION, decision_step, qd),
):
    count = 0
    for s in states:
        for a in ACTIONS:
            assert observe(step(a, s)) == abstract_step(a, observe(s))
            count += 1
    assert {observe(s) for s in states} == set(product(B, repeat=2))
    assert first_collision(states, BASE_ACTIONS, step, p) is None
    assert first_collision(states, ACTIONS, step, observe) is None
    commuting_counts[name] = count

coarse_collisions = {
    "cell": first_collision(CELL, ACTIONS, cell_step, p),
    "decision": first_collision(DECISION, ACTIONS, decision_step, p),
}
assert all(coarse_collisions.values())

words = tuple(w for length in range(HORIZON + 1)
              for w in product(ACTIONS, repeat=length))
related_pairs = tuple((c, d) for c in CELL for d in DECISION if qc(c) == qd(d))
trajectory_cases = 0
prefix_comparisons = 0
for c0, d0 in related_pairs:
    for word in words:
        c, d, z = c0, d0, qc(c0)
        assert qc(c) == qd(d) == z
        prefix_comparisons += 1
        for a in word:
            c, d, z = cell_step(a, c), decision_step(a, d), abstract_step(a, z)
            assert qc(c) == qd(d) == z
            prefix_comparisons += 1
        trajectory_cases += 1

# Enumerate every refinement of the visible-output partition on the finite cell.
# This search does not prescribe the candidate memory bit or the quotient map.
def partitions(items):
    if not items:
        yield ()
        return
    first, *rest = items
    for part in partitions(rest):
        yield ((first,),) + part
        for i in range(len(part)):
            yield part[:i] + ((first,) + part[i],) + part[i + 1:]

zero_fibre = tuple(i for i, s in enumerate(CELL) if p(s) == 0)
one_fibre = tuple(i for i, s in enumerate(CELL) if p(s) == 1)
candidate_partitions = tuple(
    left + right for left in partitions(zero_fibre) for right in partitions(one_fibre)
)
cell_index = {s: i for i, s in enumerate(CELL)}
def compatible_partition(part, actions):
    labels = {i: block for block, members in enumerate(part) for i in members}
    for a in actions:
        for members in part:
            next_blocks = {labels[cell_index[cell_step(a, CELL[i])]] for i in members}
            if len(next_blocks) != 1:
                return False
    return True

partition_results = {}
for name, actions in (("base_actions", BASE_ACTIONS), ("all_actions", ACTIONS)):
    good = [part for part in candidate_partitions if compatible_partition(part, actions)]
    counts = Counter(map(len, good))
    smallest = min(counts)
    min_parts = [part for part in good if len(part) == smallest]
    partition_results[name] = {
        "compatible_partitions": len(good),
        "by_block_count": dict(sorted(counts.items())),
        "minimum_blocks": smallest,
        "minimum_partitions": [[[CELL[i] for i in block] for block in part]
                               for part in min_parts],
    }
assert len(candidate_partitions) == 225
assert partition_results["base_actions"]["minimum_blocks"] == 2
assert partition_results["all_actions"]["minimum_blocks"] == 4
assert len(partition_results["all_actions"]["minimum_partitions"]) == 1

# Invalid variants ensure the checker rejects the claimed abstraction when an
# omitted variable actually changes an admitted action's visible consequence.
def mutated_cell_step(a, s):
    if a == "probe":
        v, m, n = s
        return m ^ n, m, 1 - n
    return cell_step(a, s)

def mutated_decision_step(a, s):
    if a == "probe":
        v, h = s
        return (h[-1] if h else 0), h + (0,)
    return decision_step(a, s)

mutation_collisions = {
    "cell_nuisance_exposed": first_collision(CELL, ACTIONS, mutated_cell_step, qc),
    "decision_last_symbol_exposed": first_collision(DECISION, ACTIONS, mutated_decision_step, qd),
}
assert all(mutation_collisions.values())

# Lack of surjectivity permits distinct extensions outside the observation image.
extension_0 = {0: 0, 1: 1, 2: 0}
extension_1 = {0: 0, 1: 1, 2: 1}
assert all(extension_0[x] == extension_1[x] == x for x in B)
assert extension_0 != extension_1

trace = []
c, d = (0, 0, 0), (0, ())
trace.append({"action": "initial", "cell": c, "decision": d, "shared": qc(c)})
for a in ("prime", "wait", "probe", "prime", "probe", "reset"):
    c, d = cell_step(a, c), decision_step(a, d)
    assert qc(c) == qd(d)
    trace.append({"action": a, "cell": c, "decision": d, "shared": qc(c)})

source_dir = ROOT / "source-snapshots"
prior_receipt = json.loads((source_dir / "PUBLIC-VERIFICATION.json").read_text(encoding="utf-8"))
source_hash_matches = []
for module in prior_receipt["modules"]:
    path = source_dir / module["source"]["path"]
    actual_hash = sha256(path.read_bytes()).hexdigest()
    expected_hash = module["source"]["sha256"]
    assert actual_hash == expected_hash
    source_hash_matches.append({
        "module": module["module"], "file": path.name,
        "actual_sha256": actual_hash, "recorded_sha256": expected_hash,
        "match": True,
    })

result = {
    "status": "PASS",
    "recorded_utc": datetime.now(timezone.utc).isoformat(),
    "evidence_kind": "author-run bounded executable checks, not an independent review or Lean proof",
    "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
    "bounds": {
        "cell_states_exhaustive": len(CELL),
        "decision_initial_histories_max_length": MAX_HISTORY,
        "decision_initial_states_checked": len(DECISION),
        "action_words_max_length": HORIZON,
        "action_words_including_empty": len(words),
        "related_initial_pairs": len(related_pairs),
        "longer_histories_and_all_horizons": "covered by the written induction, not finite enumeration",
    },
    "commuting_equation_checks": commuting_counts,
    "trajectory_cases": trajectory_cases,
    "trajectory_prefix_comparisons": prefix_comparisons,
    "coarse_observation_counterexamples": coarse_collisions,
    "visible_refinement_partitions_tested": len(candidate_partitions),
    "partition_results": partition_results,
    "invalid_variant_counterexamples": mutation_collisions,
    "nonsurjective_uniqueness_control": {
        "X": [0, 1], "Y": [0, 1, 2], "p": "inclusion", "T": "identity",
        "extension_0": extension_0, "extension_1": extension_1,
        "agree_on_image_but_not_globally": True,
    },
    "worked_trace": trace,
    "reused_source_hash_matches": source_hash_matches,
    "prior_lean_receipt_status": prior_receipt["status"],
    "prior_lean_checked_at": prior_receipt["checked_at_utc"],
    "new_lean_invocations": 0,
    "biological_validation": False,
}
(ROOT / "FINITE-CHECKS.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
print(json.dumps({
    "status": result["status"],
    "commuting_checks": commuting_counts,
    "trajectory_cases": trajectory_cases,
    "prefix_comparisons": prefix_comparisons,
    "partitions_tested": len(candidate_partitions),
    "minimum_blocks_base_all": [partition_results[n]["minimum_blocks"]
                               for n in ("base_actions", "all_actions")],
    "compatible_partition_counts": {n: partition_results[n]["compatible_partitions"]
                                    for n in partition_results},
    "mutation_controls": "both rejected",
    "pinned_sources_match_prior_receipt": True,
    "new_lean_invocations": 0,
}, indent=2))
