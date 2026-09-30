"""Finite support checks using saved systems; no tree or target-code imports."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import json
import time


def displayed_pair(codes, x, y, z, w):
    quartet = tuple(sorted((x, y, z, w)))
    target = frozenset((x, y))
    a, b, c, d = quartet
    for bit, side in ((1, (a, b)), (2, (a, c)), (4, (a, d))):
        if codes[quartet] & bit:
            side = frozenset(side)
            if target == side or target == frozenset(quartet) - side:
                return True
    return False


def rho(codes, x, y, p, q):
    quartet = tuple(sorted((x, y, p, q)))
    code = codes[quartet]
    assert code in (1, 4, 5)
    if code in (1, 4):
        return Fraction(0 if displayed_pair(codes, x, y, p, q) else 1)
    # In a four-cycle, opposite positions have distance two in cyclic order.
    return Fraction(1 if abs(quartet.index(x) - quartet.index(y)) == 2 else Fraction(1, 2))


def entry(codes, x, y, p, q):
    if x == y or frozenset((x, y)) == frozenset((p, q)):
        return Fraction(0)
    if x in (p, q) or y in (p, q):
        return Fraction(1)
    return 2 * rho(codes, x, y, p, q)


def alpha(codes, p, q, a, b, c, d):
    return (entry(codes, a, c, p, q) + entry(codes, b, d, p, q)
            - entry(codes, a, d, p, q) - entry(codes, b, c, p, q))


def run():
    started = time.monotonic()
    folder = Path(__file__).resolve().parent
    source = folder / "independent-all-level-check.json"
    source_bytes = source.read_bytes()
    saved = json.loads(source_bytes.decode("utf-8"))
    assert saved["status"] == "PASS_EXHAUSTIVE_FINITE_REPRESENTATION_CHECK"
    report = {
        "status": "IN_PROGRESS",
        "scope": "Original NANUQ anchor support in the 122 saved adjacent-copy systems on 3..6 labels; structural lifting is not checked.",
        "method": "Exact rational entries, direct displayed-pair and four-cycle adjacency tests; no tree enumeration and no target-script imports.",
        "input": source.name,
        "input_sha256": sha256(source_bytes).hexdigest(),
        "verifier_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "rows": [],
        "failure": None,
    }

    def write_receipt():
        report["elapsed_seconds"] = round(time.monotonic() - started, 3)
        (folder / "independent-support-check.json").write_text(
            json.dumps(report, indent=2) + "\n", encoding="utf-8", newline="\n")

    def require(condition, kind, n, system, gaps, anchors, **details):
        if condition:
            return
        report["status"] = "FAIL_FINITE_SUPPORT_CHECK"
        report["failure"] = {"kind": kind, "taxa": n, "system": list(system),
                             "gaps": list(gaps), "anchors": list(anchors), **details}
        write_receipt()
        print(json.dumps(report["failure"], indent=2), flush=True)
        raise SystemExit(1)

    for item in saved["rows"]:
        n = item["taxa"]
        quartets = tuple(combinations(range(n), 4))
        anchors = tuple(combinations(range(n), 2))
        systems = item["quartet_systems"]
        row = {"taxa": n, "systems": len(systems), "nonadjacent_gap_cases": 0,
               "absent_boundary_cases": 0, "present_boundary_cases": 0,
               "absent_all_anchor_zero_checks": 0, "boundary_anchor_formula_checks": 0,
               "pendant_anchor_checks": 0,
               "boundary_anchor_values_when_absent": {},
               "boundary_anchor_values_when_present": {}}
        value_histograms = {False: Counter(), True: Counter()}
        report["rows"].append(row)
        for system in systems:
            assert len(system) == len(quartets) and all(code in (1, 4, 5) for code in system)
            codes = dict(zip(quartets, system))
            for i, j in combinations(range(n), 2):
                a, b, c, d = i, (i+1) % n, j, (j+1) % n
                if len({a, b, c, d}) != 4:
                    continue
                row["nonadjacent_gap_cases"] += 1
                present = displayed_pair(codes, b, c, a, d)
                row["present_boundary_cases" if present else "absent_boundary_cases"] += 1
                actual = alpha(codes, a, d, a, b, c, d)
                expected = 2 - 2 * rho(codes, b, c, a, d)
                row["boundary_anchor_formula_checks"] += 1
                require(actual == expected, "boundary_anchor_formula", n, system, (i, j), (a, d),
                        actual=str(actual), expected=str(expected))
                require((actual > 0) == present, "boundary_anchor_support", n, system, (i, j), (a, d),
                        boundary_quartet_present=present, alpha=str(actual))
                value_histograms[present][str(actual)] += 1
                if not present:
                    for p, q in anchors:
                        value = alpha(codes, p, q, a, b, c, d)
                        row["absent_all_anchor_zero_checks"] += 1
                        require(value == 0, "absent_boundary_nonzero_anchor", n, system, (i, j), (p, q),
                                boundary_quartet=[[b, c], [a, d]], alpha=str(value))
            # Orient adjacent gaps so their shared tip is b=c. This enumerates
            # each pendant boundary once, including the circular wraparound.
            for i in range(n):
                j = (i+1) % n
                a, b, c, d = i, j, j, (i+2) % n
                value = alpha(codes, a, d, a, b, c, d)
                row["pendant_anchor_checks"] += 1
                require(value == 2, "pendant_boundary_anchor", n, system, (i, j), (a, d), alpha=str(value))
        row["boundary_anchor_values_when_absent"] = dict(sorted(value_histograms[False].items()))
        row["boundary_anchor_values_when_present"] = dict(sorted(value_histograms[True].items()))
        assert row["nonadjacent_gap_cases"] == len(systems) * n * (n-3) // 2
        assert row["pendant_anchor_checks"] == len(systems) * n
        assert row["absent_all_anchor_zero_checks"] == row["absent_boundary_cases"] * len(anchors)

    for key in ("systems", "nonadjacent_gap_cases", "absent_boundary_cases", "present_boundary_cases",
                "absent_all_anchor_zero_checks", "boundary_anchor_formula_checks", "pendant_anchor_checks"):
        report["total_" + key] = sum(row[key] for row in report["rows"])
    report["status"] = "PASS_FINITE_ZERO_CERTIFICATE_AND_BOUNDARY_ANCHOR_FORMULA"
    write_receipt()
    print(json.dumps(report, indent=2), flush=True)


if __name__ == "__main__":
    run()
