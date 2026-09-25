"""Finite falsification checks for an UNPROVED full-height formula.

Neither a successful run nor the candidate's fast evaluator proves the formula.
The stored values came from independent exact frontier computation. Fresh
positive starts below use the already-proved interval transition, not this
formula, to compute extinction. Cases exceeding the explicit cap are reported.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[2]


def bit(n: int) -> int:
    return n.bit_count() % 2


def candidate(v: int) -> int:
    if v < 0:
        raise ValueError("start must be nonnegative")
    n = v // 2
    q = (n + 1) & -(n + 1)
    r = q.bit_length() - 1
    h = ((n + 1) // q - 1) // 2
    t, u = bit(h), bit(h + 1)
    special = h % 4 == 1 and bit(h // 4) == 0 and bit(h // 4 + 1) == 1
    if v % 2 == 0:
        if t:
            return 1 - r % 2
        return 7 - 2*u if q == 2 else (4 - 2*u)*q - 1
    if not t:
        return 0
    if not u:
        return 4*q - 1
    return 16*q - 3 if special else 10*q - 1


def coordinates(n: int) -> tuple[int, ...]:
    t, u = bit(n), bit(n + 1)
    numerator = candidate(4*n + 1) - t
    assert numerator % 2 == 0
    return (1, t, u, t*u, candidate(n), candidate(2*n), candidate(2*n+1),
            numerator//2, candidate(4*n+2), candidate(4*n+3))


def transition(z: tuple[int, ...], digit: int) -> tuple[int, ...]:
    one, t, u, v, length, e, o, x, f, c = z
    if digit == 0:
        return (one, t, 1-t, 0, e, 3-2*t-2*u+2*v, 2*x+t, t,
                7-7*t-2*u+2*v, 5*x+2*t-3*v)
    if digit == 1:
        return (one, 1-t, u, u-v, o, f, c, 3*u-12*v-2*e+2*x+f,
                t+3*u+15*v+4*e-4*x, 3*c-2*o)
    raise ValueError("digit must be binary")


def actual_capped(start: int, cap: int) -> tuple[int | None, int]:
    if start == 0:
        frontier = {0}
        for k in range(cap):
            target = bit(k)
            frontier = {child for parent in frontier for step in (1, 2)
                        if (child := parent + step) >= 2
                        and (bit(child) if step == 1 else 1-bit(child)) == target}
            if not frontier:
                return k, k+1
        return None, cap
    lo, hi = start, start+1
    for k in range(cap):
        target = bit(k)
        lo += 1 if bit(lo+1) == target else 2
        hi += 1 if bit(hi+1) == target else 2
        if lo == hi:
            return k, k+1
    return None, cap


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--fresh", type=int, default=2200)
    parser.add_argument("--cap", type=int, default=20000)
    args = parser.parse_args()
    if args.fresh < 0 or args.cap < 1:
        parser.error("fresh must be nonnegative and cap must be positive")
    path = ROOT / "checks/scan-bitset-131072.json.gz"
    with gzip.open(path, "rt", encoding="utf-8") as stream:
        data = json.load(stream)
    assert data["all_lengths_exact"] is True
    expected = data["lengths_or_lower_bounds_by_start"]
    comparisons = 0
    for start, length in enumerate(expected):
        if length is None:
            assert start == 0
            continue
        assert candidate(start) == length, (start, candidate(start), length)
        comparisons += 1
    assert actual_capped(0, 10)[0] == candidate(0) == 1
    for n in range(8192):
        for digit in (0, 1):
            assert transition(coordinates(n), digit) == coordinates(2*n+digit), (n, digit)
    rng = random.Random(20260925)
    starts = rng.sample(range(131072, 10**9), args.fresh)
    # Deliberately include long near-extremal cases; report cap exhaustion.
    starts += [3*2**n-1 for n in range(15, 29)]
    checked, advances, skipped = 0, 0, []
    for start in starts:
        actual, work = actual_capped(start, args.cap)
        advances += work
        if actual is None:
            skipped.append(start)
            continue
        assert actual == candidate(start), (start, actual, candidate(start))
        checked += 1
    report = {
        "status": "finite checks passed; full-height formula remains unproved",
        "stored_file_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "stored_exact_comparisons": comparisons,
        "start_zero_direct_check": True,
        "coordinate_transition_comparisons": 2*8192,
        "coordinate_equalities_checked": 10*2*8192,
        "fresh_seed": 20260925,
        "fresh_cases_checked": checked,
        "fresh_boundary_advances": advances,
        "fresh_max_start_considered": max(starts),
        "per_case_advance_cap": args.cap,
        "skipped_at_cap": skipped,
        "universal_lean_theorem": None,
    }
    out = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(out, encoding="utf-8")
    print(out, end="")


if __name__ == "__main__":
    main()
