"""Exact finite-path search in the Thue-Morse avoiding population.

No result from this program proves a claim for all starting vertices. The
quadratic stopping bound used below is proved in NOTE.md.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def thue_morse(n: int) -> int:
    if n < 0:
        raise ValueError("index must be nonnegative")
    return n.bit_count() & 1


def proved_bound(v: int) -> int:
    """An inclusive upper bound for the number of matching edges."""
    if v < 0:
        raise ValueError("start must be nonnegative")
    m, odd = divmod(v, 2)
    if odd:
        return 2 * m * m + 8 * m + 5
    return 2 * m * m + 7 * m + 3


def successors(vertex: int, target_bit: int) -> tuple[int, ...]:
    """Matching outgoing neighbors under the paper's edge definition."""
    out = []
    w = vertex + 1
    if w >= 2 and thue_morse(w) == target_bit:
        out.append(w)
    w = vertex + 2
    if 1 - thue_morse(w) == target_bit:
        out.append(w)
    return tuple(out)


def path_length(start: int, *, statistics: bool = False) -> int | dict:
    """Return exact maximum number of matching edges from ``start``.

    The frontier at depth k contains every reachable endpoint after k labels.
    It is finite. The proved quadratic bound ensures the loop must terminate.
    """
    if start < 0:
        raise ValueError("start must be nonnegative")
    frontier = {start}
    width_max = 1
    visited_states = 1
    for depth in range(proved_bound(start) + 1):
        bit = thue_morse(depth)
        next_frontier = {
            nxt
            for vertex in frontier
            for nxt in successors(vertex, bit)
        }
        if not next_frontier:
            if statistics:
                return {
                    "start": start,
                    "length": depth,
                    "maximum_frontier_width": width_max,
                    "visited_depth_endpoint_pairs": visited_states,
                }
            return depth
        frontier = next_frontier
        width_max = max(width_max, len(frontier))
        visited_states += len(frontier)
    raise AssertionError("the proved quadratic bound was exceeded")


def scan(limit: int) -> dict:
    """Exhaustively check starts 0 <= v < limit."""
    if limit < 1:
        raise ValueError("limit must be positive")
    values = [path_length(v) for v in range(limit)]
    assert all(isinstance(value, int) for value in values)
    exceptions = [
        {"start": v, "length": values[v]}
        for v in range(1, limit)
        if 3 * values[v] > 8 * v - 1
    ]
    equality = [
        {"start": v, "length": values[v]}
        for v in range(1, limit)
        if 3 * values[v] == 8 * v - 1
    ]
    maximum = max(values)
    return {
        "population": "P_t, Section 2 of A classification of biologically unavoidable sequences",
        "start_range": [0, limit - 1],
        "target_index_start": 0,
        "lengths_by_start": values,
        "first_16_lengths": values[:16],
        "maximum_length": maximum,
        "maximum_length_starts": [v for v, value in enumerate(values) if value == maximum],
        "linear_inequality_checked_for_starts": [1, limit - 1],
        "linear_inequality": "3*L(v) <= 8*v-1",
        "linear_inequality_counterexamples": exceptions,
        "linear_inequality_equality_cases": equality,
        "proof_status_of_linear_inequality": "conjectural; finite scan only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=8192)
    parser.add_argument("--output", type=Path, help="write summary JSON to this path")
    args = parser.parse_args()
    result = scan(args.limit)
    output = json.dumps(result, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
