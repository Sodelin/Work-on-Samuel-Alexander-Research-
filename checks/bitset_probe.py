"""Independent bitset probe of the provisional linear path-length inequality.

This checks a finite range only. Its bitset transition is distinct from the
set-of-endpoints implementation in explore.py.
"""

from __future__ import annotations

import argparse
import gzip
import json
from pathlib import Path

from explore import thue_morse


def make_masks(max_vertex: int) -> tuple[int, int]:
    width = max_vertex // 8 + 1
    zero = bytearray(width)
    one = bytearray(width)
    for w in range(2, max_vertex + 1):
        target = one if thue_morse(w) else zero
        target[w // 8] |= 1 << (w % 8)
    return int.from_bytes(zero, "little"), int.from_bytes(one, "little")


def linear_budget(v: int) -> int:
    if v < 1:
        raise ValueError("provisional inequality is stated only for v >= 1")
    return (8 * v - 1) // 3


def probe_one(v: int, masks: tuple[int, int]) -> tuple[int, bool]:
    """Return (exact L, False) if L<=budget; else (budget+1, True)."""
    budget = linear_budget(v)
    frontier = 1 << v
    for depth in range(budget + 1):
        bit = thue_morse(depth)
        # Bit w of frontier<<1 corresponds to w-1 -> w. Bit w of
        # frontier<<2 corresponds to w-2 -> w. Masks exclude 0 and 1.
        next_frontier = ((frontier << 1) & masks[bit]) | (
            (frontier << 2) & masks[1 - bit]
        )
        if not next_frontier:
            return depth, False
        frontier = next_frontier
    return budget + 1, True


def scan(limit: int) -> dict:
    if limit < 2:
        raise ValueError("limit must be at least 2")
    largest_start = limit - 1
    max_vertex = largest_start + 2 * (linear_budget(largest_start) + 1)
    masks = make_masks(max_vertex)
    values = [None]
    counterexamples = []
    equality = []
    for v in range(1, limit):
        length_or_lower_bound, exceeded = probe_one(v, masks)
        values.append(length_or_lower_bound)
        if exceeded:
            counterexamples.append({"start": v, "length_at_least": length_or_lower_bound})
        elif length_or_lower_bound == linear_budget(v):
            equality.append({"start": v, "length": length_or_lower_bound})
    return {
        "method": "bitset frontier; finite provisional-bound probe",
        "start_range": [1, limit - 1],
        "provisional_inequality": "3*L(v) <= 8*v-1",
        "counterexamples": counterexamples,
        "equality_cases": equality,
        "lengths_or_lower_bounds_by_start": values,
        "all_lengths_exact": not counterexamples,
        "proof_status": "finite computation only",
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=32768)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = json.dumps(scan(args.limit), indent=2) + "\n"
    if args.output:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        if args.output.suffix == ".gz":
            with args.output.open("wb") as raw:
                with gzip.GzipFile(filename="", fileobj=raw, mode="wb", mtime=0) as packed:
                    packed.write(output.encode("utf-8"))
        else:
            args.output.write_text(output, encoding="utf-8")
    else:
        print(output, end="")


if __name__ == "__main__":
    main()
