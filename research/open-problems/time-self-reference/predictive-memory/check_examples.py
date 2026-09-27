"""Exact arithmetic checks; all inputs are stipulated, not biological data."""
from collections import deque
from fractions import Fraction as F
from itertools import product
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ACTIONS = ("wait", "prime", "probe", "reset")
STATES = tuple(product((0, 1), repeat=3))


def transition(a, s):
    v, m, n = s
    return {
        "wait": (v, m, 1 - n), "prime": (v, 1 - m, 1 - n),
        "probe": (m, m, 1 - n), "reset": (0, 0, 1 - n),
    }[a]


def partition_refinement(actions):
    colors = {s: s[0] for s in STATES}
    sizes = [len(set(colors.values()))]
    for depth in range(len(STATES)):
        signatures = {s: (s[0], tuple(colors[transition(a, s)] for a in actions)) for s in STATES}
        palette = {signature: k for k, signature in enumerate(sorted(set(signatures.values())))}
        new = {s: palette[signatures[s]] for s in STATES}
        stable = all((colors[x] == colors[y]) == (new[x] == new[y]) for x in STATES for y in STATES)
        sizes.append(len(set(new.values())))
        if stable:
            # This is the global E_depth = E_(depth+1) condition used by Lean.
            return {"stable_depth": depth, "partition_sizes": sizes,
                    "codes": [[list(s), new[s]] for s in STATES]}, new
        colors = new
    raise AssertionError("Finite partition refinement did not stabilize")


def distinguishing_word(x, y, actions):
    todo = deque([(x, y, ())])
    visited = set()
    while todo:
        left, right, word = todo.popleft()
        if (left, right) in visited:
            continue
        visited.add((left, right))
        if left[0] != right[0]:
            return list(word)
        todo.extend((transition(a, left), transition(a, right), word + (a,)) for a in actions)
    return None


def main():
    full, colors = partition_refinement(ACTIONS)
    passive, passive_colors = partition_refinement(("wait", "prime", "reset"))
    assert full["partition_sizes"] == [2, 4, 4]
    assert passive["partition_sizes"] == [2, 2]
    for x in STATES:
        for y in STATES:
            word = distinguishing_word(x, y, ACTIONS)
            assert (word is None) == (colors[x] == colors[y])
            assert (colors[x] == colors[y]) == (x[:2] == y[:2])
            assert (passive_colors[x] == passive_colors[y]) == (x[0] == y[0])
    witness = distinguishing_word((0, 0, 0), (0, 1, 0), ACTIONS)
    assert witness == ["probe"]

    # H and permanent type theta are independent, uniformly randomized bits.
    table = [(h, theta, h ^ theta, theta, F(1, 4)) for h, theta in product((0, 1), repeat=2)]
    selected = {}
    marginal = {}
    for h in (0, 1):
        rows = [r for r in table if r[0] == h]
        mass = sum(r[4] for r in rows)
        marginal[h] = sum(r[4] * r[3] for r in rows) / mass
        kept = [r for r in rows if r[2] == 0]
        kept_mass = sum(r[4] for r in kept)
        selected[h] = sum(r[4] * r[3] for r in kept) / kept_mass
        assert kept_mass == F(1, 4)  # no zero-support conditioning
    assert marginal == {0: F(1, 2), 1: F(1, 2)}
    assert selected == {0: F(0), 1: F(1)}

    # A stable type with a prespecified time profile, independently sampled
    # responses conditional on that type. It never learns from its responses.
    schedules = ((F(1, 2),) * 3 + (F(1, 4), F(3, 4), F(1, 2), F(3, 4)),
                 (F(1, 2),) * 3 + (F(3, 4), F(1, 4), F(1, 2), F(1, 4)))
    distribution = []
    for theta, probs in enumerate(schedules):
        for responses in product((0, 1), repeat=7):
            weight = F(1, 2)
            for y, p in zip(responses, probs):
                weight *= p if y else 1 - p
            distribution.append((theta, responses, weight))
    assert sum(row[2] for row in distribution) == 1
    predictions = []
    for history in ((0, 0, 0, 0, 1), (0, 0, 0, 1, 0)):
        rows = [(theta, ys, mass) for theta, ys, mass in distribution
                if ys[:5] == history and ys[5] == 0]
        denominator = sum(mass for _, _, mass in rows)
        pred = sum(mass * ys[6] for _, ys, mass in rows) / denominator
        assert denominator == F(5, 256)
        predictions.append(str(pred))
    assert predictions == ["7/10", "3/10"]
    output = {
        "status": "PASS", "evidence_class": "invented mathematical inputs, exact rational enumeration",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "full_interventions": full, "passive_interventions": passive,
        "all_ordered_cell_pairs_checked": 64, "shortest_memory_witness": witness,
        "randomized_history_selection_counterexample": {
            "rows_H_type_V_Y_mass": [[h, t, v, y, str(m)] for h, t, v, y, m in table],
            "marginal_response_probability": {h: str(v) for h, v in marginal.items()},
            "response_probability_given_V_zero": {h: str(v) for h, v in selected.items()},
        },
        "stable_timed_type_predictions": predictions,
        "biological_observations_used": 0, "fitted_models": 0,
    }
    (HERE / "verification" / "EXACT-EXAMPLES.json").write_text(json.dumps(output, indent=2) + "\n", encoding="utf-8")
    print("PASS: global finite-state refinement, 64 ordered pairs, two exact selection/type counterexamples")


if __name__ == "__main__":
    main()
