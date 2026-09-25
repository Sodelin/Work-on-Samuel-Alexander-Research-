"""Diagnostic checks for the proved interval/coalescence reduction.

This checker does not prove the conjectured sharp bound. It independently
computes a maximum length by following two deterministic boundary trajectories,
and compares with the existing stored set-frontier results. The universal
interval theorem is proved in ThueMorseBound.lean, not by this finite check.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]


def t(n: int) -> int:
    return n.bit_count() % 2


def boundary(x: int, bit: int) -> int:
    return x + 1 if t(x + 1) == bit else x + 2


def interval_length(start: int) -> int:
    if start < 1:
        raise ValueError("the formal interval theorem here assumes start >= 1")
    lo, hi = start, start + 1
    # This is the prior proved quadratic stopping guard, not the conjecture.
    guard = (start + 1) * (start + 6) // 2
    for k in range(guard + 1):
        bit = t(k)
        lo, hi = boundary(lo, bit), boundary(hi, bit)
        assert lo <= hi
        if lo == hi:
            # The first empty frontier is at depth k+1; length k survives.
            return k
    raise AssertionError("prior proved quadratic bound was exceeded")


def paired_formula(x: int, bit: int) -> int:
    m, odd = divmod(x, 2)
    if t(m + 1) == bit:
        return 2 * m + 3
    if odd:
        return 2 * m + (5 if t(m + 2) == bit else 4)
    return 2 * m + (4 if t(m) == bit else 2)


def direct_frontier(start: int, depth: int) -> set[int]:
    frontier = {start}
    for k in range(depth):
        out: set[int] = set()
        for x in frontier:
            if x + 1 >= 2 and t(x + 1) == t(k):
                out.add(x + 1)
            if t(x + 2) != t(k):
                out.add(x + 2)
        frontier = out
    return frontier


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    stored = json.loads((REPO / "checks/scan-8192.json").read_text())
    expected = stored["lengths_by_start"]
    for start in range(1, len(expected)):
        actual = interval_length(start)
        assert actual == expected[start], (start, actual, expected[start])

    frontier_cases = 0
    for start in range(1, 128):
        lo, hi = start, start + 1
        # Include several empty steps to check that coalescence persists.
        for depth in range(expected[start] + 4):
            actual = direct_frontier(start, depth)
            assert actual == set(range(lo, hi)), (start, depth, lo, hi, actual)
            bit = t(depth)
            lo, hi = boundary(lo, bit), boundary(hi, bit)
            frontier_cases += 1

    for x in range(4096):
        for bit in (0, 1):
            assert boundary(boundary(x, bit), 1 - bit) == paired_formula(x, bit)

    result = {
        "status": "all diagnostic finite checks passed",
        "proof_status_of_sharp_bound": "proved separately; this checker is finite corroboration only",
        "sharp_proof": "lean/SamuelAlexanderResearch/SharpThueMorse.lean",
        "stored_set_engine_length_comparisons": len(expected) - 1,
        "stored_set_engine_start_range": [1, len(expected) - 1],
        "direct_frontier_state_comparisons": frontier_cases,
        "paired_formula_cases": 4096 * 2,
        "universal_proof": "lean/SamuelAlexanderResearch/ThueMorseBound.lean",
    }
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
