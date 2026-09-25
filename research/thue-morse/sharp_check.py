"""Finite corroboration of the written sharp Thue--Morse proof.

Replay its complete auxiliary boundary-trajectory run patterns for n=0..8,
check their extinction indexing, compare the claimed inequality/equality set
with the existing 8192-start scan, and check H(v) for v=0..255. This program
does not prove any universal statement and does not expand the existing scan.
It independently implements the actual boundary recurrence without importing
the run-pattern formulas or the other interval checker.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


REPO = Path(__file__).resolve().parents[2]


def require(condition: bool, detail: object) -> None:
    # Keep diagnostic failures enabled even when Python runs with -O.
    if not condition:
        raise AssertionError(detail)


def actual_next(vertex: int, time: int) -> int:
    source_bit = (vertex + 1).bit_count() % 2
    target_bit = time.bit_count() % 2
    return vertex + (1 if source_bit == target_bit else 2)


def claimed_advances(q: int, start: int) -> list[int]:
    if start == 6 * q - 1:
        advances = [1] * (4 * q)
    elif q == 1:
        advances = [2, 2, 1, 1]
    else:
        r = q // 2
        advances = (
            [2] * (2 * r)
            + [1]
            + [2] * (r - 1)
            + [1] * (2 * r)
            + [2] * (3 * r)
        )
    r = q
    while r:
        advances.extend([2] * r + [1] * r)
        r //= 2
    return advances


def replay_run_patterns() -> dict:
    trajectory_count = 0
    advance_count = 0
    for exponent in range(9):
        q = 1 << exponent
        end_time = 8 * q - 2
        for start in (6 * q - 1, 3 * q):
            claimed = claimed_advances(q, start)
            require(len(claimed) == end_time, (q, start, "run-list length"))
            vertex = start
            first_zero = None
            for time, advance in enumerate(claimed):
                actual = actual_next(vertex, time)
                require(
                    actual == vertex + advance,
                    (q, start, time, vertex, "claimed advance", advance, "actual", actual),
                )
                vertex = actual
                depth = time + 1
                offset = vertex - 2 * depth
                require(offset >= 0, (q, start, depth, "negative offset"))
                if offset == 0 and first_zero is None:
                    first_zero = depth
                if depth == 4 * q:
                    require(vertex == 10 * q - 1, (q, start, "descent entry"))
                if depth == end_time - 1:
                    require(offset == 1, (q, start, "last-positive offset", offset))
                advance_count += 1
            require(first_zero == end_time, (q, start, "first zero", first_zero))
            require(vertex == 2 * end_time, (q, start, "final baseline"))
            trajectory_count += 1
    return {
        "dyadic_exponent_range": [0, 8],
        "q_range": [1, 256],
        "start_families": ["6q-1", "3q"],
        "complete_trajectories": trajectory_count,
        "advance_comparisons": advance_count,
        "descent_entry_checks": trajectory_count,
        "last_positive_offset_checks": trajectory_count,
        "first_zero_time_checks": trajectory_count,
        "last_positive_time": "8q-3, offset 1",
        "first_zero_time": "8q-2, offset 0",
    }


def check_existing_scan() -> dict:
    scan = json.loads((REPO / "checks/scan-8192.json").read_text(encoding="utf-8"))
    lengths = scan["lengths_by_start"]
    require(scan["start_range"] == [0, 8191], "unexpected stored scan range")
    require(scan["target_index_start"] == 0, "unexpected target phase")
    require(len(lengths) == 8192, "unexpected stored scan length")
    require(all(type(n) is int and n >= 0 for n in lengths), "invalid stored lengths")

    violations = [v for v in range(1, 8192) if 3 * lengths[v] > 8 * v - 1]
    require(not violations, ("stored sharp-inequality violations", violations))
    observed_equalities = [v for v in range(1, 8192) if 3 * lengths[v] == 8 * v - 1]
    expected_equalities = []
    q = 1
    while 3 * q - 1 < 8192:
        start = 3 * q - 1
        expected_equalities.append(start)
        require(lengths[start] == 8 * q - 3, (start, "equality-family length"))
        q *= 2
    require(
        observed_equalities == expected_equalities,
        ("exact equality set", observed_equalities, expected_equalities),
    )
    return {
        "input": "checks/scan-8192.json",
        "new_path_scan_performed": False,
        "start_range": [1, 8191],
        "inequality_checks": 8191,
        "inequality_violations": [],
        "exact_equality_vertices": observed_equalities,
        "equality_family_length_checks": len(expected_equalities),
    }


def claimed_hitting_time(start: int) -> int:
    if start == 0:
        return 0
    if start <= 2:
        return 2
    q = 1
    while 6 * q <= start:
        q *= 2
    return 8 * q - 2


def check_small_hitting_times() -> dict:
    maximum = 0
    for start in range(256):
        vertex = start
        # A fixed diagnostic ceiling bounds the work; no larger start scan.
        for time in range(1025):
            if vertex == 2 * time:
                actual = time
                break
            vertex = actual_next(vertex, time)
        else:
            raise AssertionError((start, "fixed diagnostic ceiling exceeded"))
        require(actual == claimed_hitting_time(start), (start, "H(v)", actual))
        maximum = max(maximum, actual)
    return {
        "start_range": [0, 255],
        "first_hitting_time_checks": 256,
        "fixed_time_ceiling": 1024,
        "maximum_observed_hitting_time": maximum,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = {
        "status": "all finite sharp-proof diagnostic checks passed",
        "evidence_scope": "finite corroboration; this output is not a universal proof",
        "written_universal_proof": "research/thue-morse/NEXT-INVARIANT.md",
        "lean_proof_status": "not assessed by this checker",
        "run_patterns": replay_run_patterns(),
        "existing_scan_comparison": check_existing_scan(),
        "small_baseline_hitting_times": check_small_hitting_times(),
    }
    output = json.dumps(result, indent=2) + "\n"
    if args.output:
        args.output.write_text(output, encoding="utf-8")
    print(output, end="")


if __name__ == "__main__":
    main()
