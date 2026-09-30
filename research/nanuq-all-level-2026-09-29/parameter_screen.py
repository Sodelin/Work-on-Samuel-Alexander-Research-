"""Bounded exact screen, not a proof of a universal parameter theorem.

For one displayed quartet use (cherry, separated) scores; for two displayed
quartets use (adjacent, opposite) scores. This agrees with NANUQ+ Definition
3.1 on level-1 networks; using it on level-2 is an explicitly chosen extension.
"""
import hashlib
import importlib.util
import json
from fractions import Fraction as F
from itertools import combinations, permutations, product
from pathlib import Path

BASE = Path(r"C:\Users\Owner\Documents\Alexander-Open-Questions-2026-09-29\field-priorities\nanuq\exact_networks.py")
spec = importlib.util.spec_from_file_location("nanuq_existing_exact", BASE)
ex = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ex)


def distance(qs, labels, scores):
    d = {(x, x): F(0) for x in labels}
    for x, y in combinations(labels, 2):
        value = F(2 * len(labels) - 4)
        for z, w in combinations([v for v in labels if v not in (x, y)], 2):
            splits = qs[tuple(sorted((x, y, z, w)))]
            separate = sum((x in s) != (y in s) for s in splits)
            assert 1 <= len(splits) <= 2
            ix = separate if len(splits) == 1 else (2 if separate == 1 else 3)
            value += 2 * scores[ix]
        d[x, y] = d[y, x] = value
    return d


def circular_orders(labels):
    first, *rest = labels
    for tail in permutations(rest):
        if tail[0] < tail[-1]:
            yield (first,) + tail


def anchor_screen(cherry=F(1, 2)):
    count = 0
    coefficients = 0
    for total in range(1, 7):
        for arms in product(range(total + 1), repeat=4):
            if sum(arms) != total:
                continue
            net = ex.theta(arms)
            order = net.validate()["circular_order"]
            qs, _ = ex.quartet_system(net)
            count += 1
            for p, q in combinations(order, 2):
                d = {(x, x): F(0) for x in order}
                for x, y in combinations(order, 2):
                    if {x, y} == {p, q}:
                        value = F(0)
                    elif {x, y} & {p, q}:
                        value = F(1)
                    else:
                        splits = qs[tuple(sorted((x, y, p, q)))]
                        separated = sum((x in s) != (y in s) for s in splits)
                        ix = separated if len(splits) == 1 else (2 if separated == 1 else 3)
                        value = 2 * (cherry, F(1), F(1, 2), F(1))[ix]
                    d[x, y] = d[y, x] = value
                for split, alpha, ij in ex.coefficients(d, order):
                    coefficients += 1
                    if alpha < 0:
                        return {"all_nonnegative": False, "templates_checked": count, "coefficients_checked": coefficients,
                                "witness": {"arms": arms, "order": order, "anchors": [p, q], "split": split,
                                            "boundary_indices": ij, "alpha": str(alpha)}}
    return {"all_nonnegative": True, "templates_checked": count, "coefficients_checked": coefficients}


def support_screen():
    count = 0
    first_extra = None
    first_missing = None
    endpoint_losses = 0
    for total in range(2, 7):
        for arms in product(range(total + 1), repeat=4):
            if sum(arms) != total:
                continue
            net = ex.theta(arms)
            order = net.validate()["circular_order"]
            qs, trees = ex.quartet_system(net)
            expected = set().union(*trees)
            mid = distance(qs, order, (F(1, 2), F(1), F(1, 2), F(1)))
            end = distance(qs, order, (F(1), F(1), F(1, 2), F(1)))
            got = {s for s, a, _ in ex.coefficients(mid, order) if a > 0}
            end_got = {s for s, a, _ in ex.coefficients(end, order) if a > 0}
            if got - expected and first_extra is None:
                first_extra = {"arms": arms, "extra_splits": sorted(got - expected)}
            if expected - got and first_missing is None:
                first_missing = {"arms": arms, "missing_splits": sorted(expected - got)}
            endpoint_losses += bool(expected - end_got)
            count += 1
    return {"templates_checked": count, "first_extra_at_half": first_extra, "first_missing_at_half": first_missing,
            "templates_with_endpoint_support_loss": endpoint_losses}


def scan():
    records = []
    counterexample = None
    count = 0
    for total in range(2, 5):
        for arms in product(range(total + 1), repeat=4):
            if sum(arms) != total:
                continue
            net = ex.theta(arms)
            admission = net.validate()
            labels = sorted(net.leaves)
            order = admission["circular_order"]
            qs, _ = ex.quartet_system(net)
            ordinary = distance(qs, labels, (F(0), F(1), F(1, 2), F(1)))
            assert ordinary == ex.distance(qs, labels)
            modified = distance(qs, labels, (F(1, 2), F(1), F(1, 2), F(1)))
            negatives = [(s, str(a), ij) for s, a, ij in ex.coefficients(modified, order) if a < 0]
            count += 1
            if negatives:
                admissible = []
                checked = 0
                for other in circular_orders(labels):
                    checked += 1
                    if all(a >= 0 for _, a, _ in ex.coefficients(modified, other)):
                        admissible.append(other)
                rec = {"arms": arms, "admission": admission, "negative_coefficients_in_network_order": negatives,
                       "all_circular_orders_checked": checked, "nonnegative_orders": admissible,
                       "labels": labels, "distance_matrix": [[str(modified[x, y]) for y in labels] for x in labels]}
                records.append(rec)
                if not admissible:
                    counterexample = rec
                    break
        if counterexample:
            break
    return {"status": "bounded_parameter_screen", "existing_checker_sha256": hashlib.sha256(BASE.read_bytes()).hexdigest(),
            "parameter": ["1/2", "1", "1/2", "1"], "templates_checked": count,
            "failures_of_network_order": records, "no_circular_order_witness": counterexample,
            "scope": "A failure rules out a blanket circular-decomposition claim for this parameter under the stated quartet rule. It does not resolve the paper's broad parametric-family open problem."}


if __name__ == "__main__":
    result = scan()
    result["modified_anchor_screen"] = anchor_screen()
    result["endpoint_anchor_screen"] = anchor_screen(F(1))
    result["support_screen"] = support_screen()
    target = Path(__file__).with_name("parameter-screen.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    witness = result["no_circular_order_witness"]
    print(json.dumps({"templates_checked": result["templates_checked"], "modified_anchor_screen": result["modified_anchor_screen"], "endpoint_anchor_screen": result["endpoint_anchor_screen"], "support_screen": result["support_screen"], "network_order_failures": len(result["failures_of_network_order"]),
                      "no_circular_order_witness": witness, "receipt": str(target)}, indent=2))
