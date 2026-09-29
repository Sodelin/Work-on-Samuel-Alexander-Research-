"""Exact finite illustration of CALIBRATION-BOUND.md; Python standard library."""
from fractions import Fraction as Q
from itertools import product
import json


def distribution(n, e):
    return {bits: e ** sum(bits) * (1 - e) ** (n - sum(bits))
            for bits in product((0, 1), repeat=n)}


def errors(dist, decision):
    zero = (0,) * len(next(iter(dist)))
    alpha = decision[zero]
    beta = sum((prob * (1 - decision[bits]) for bits, prob in dist.items()), Q(0))
    return alpha, beta


def verify(n, e):
    dist = distribution(n, e)
    assert sum(dist.values(), Q(0)) == 1
    zero = (0,) * n
    q = (1 - e) ** n
    assert dist[zero] == q
    sum_rule = {bits: Q(int(any(bits))) for bits in dist}
    minimax_rule = {bits: Q(1) if any(bits) else q / (1 + q) for bits in dist}
    a, b = errors(dist, sum_rule)
    assert a + b == q
    ma, mb = errors(dist, minimax_rule)
    assert ma == mb == q / (1 + q)
    tested = 0
    if n <= 3:
        outcomes = list(dist)
        for actions in product((Q(0), Q(1)), repeat=len(outcomes)):
            da, db = errors(dist, dict(zip(outcomes, actions)))
            assert da + db >= q
            assert max(da, db) >= q / (1 + q)
            tested += 1
    return {"trials": n, "branch_probability": str(e), "all_zero_probability": str(q),
            "optimal_sum_of_errors": str(a + b), "optimal_worst_error": str(ma),
            "deterministic_rules_exhausted": tested}


if __name__ == "__main__":
    rows = [verify(n, e) for n in (0, 1, 2, 3, 8) for e in (Q(1, 2), Q(1, 10), Q(1, 100))]
    print(json.dumps({"status": "PASS", "cases": rows,
                      "scope": "Exact finite enumeration; not a Lean proof or novelty claim"}, indent=2))
