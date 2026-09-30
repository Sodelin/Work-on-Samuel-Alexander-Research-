"""All-level proof-route test via plane trees and adjacent paired tips.

This is independent of the graph/switching evaluator. It enumerates plane
binary trees for <=6 cyclically ordered taxa with one or two adjacent copies
of each taxon. Two copies represent the two incoming choices of a pendant
hybrid. An unproved source-to-representation bridge remains a proof obligation.
Exact quartet systems are deduplicated by OR dynamic programming over all
interval tree splits. No numerical randomness or floating point is used.
"""
import json
from functools import lru_cache
from itertools import combinations
from math import comb
from pathlib import Path


def systems(n, duplicated):
    tips = tuple(x for x in range(n) for _ in range(2 if (duplicated >> x) & 1 else 1))
    qs = tuple(combinations(range(n), 4))

    @lru_cache(None)
    def contribution(lo, hi):
        left = sum(1 << x for x in set(tips[lo:hi + 1]))
        right = sum(1 << x for x in set(tips[:lo] + tips[hi + 1:]))
        answer = 0
        for qi, (a, b, c, d) in enumerate(qs):
            for topology, (u, v, w, z) in enumerate(((a, b, c, d), (a, c, b, d), (a, d, b, c))):
                first, second = (1 << u) | (1 << v), (1 << w) | (1 << z)
                if ((left & first == first and right & second == second) or
                        (left & second == second and right & first == first)):
                    answer |= 1 << (3 * qi + topology)
        return answer

    @lru_cache(None)
    def interval(lo, hi):
        if lo == hi:
            return {0: lo}
        out = {}
        here = contribution(lo, hi)
        for mid in range(lo, hi):
            for a, ta in interval(lo, mid).items():
                for b, tb in interval(mid + 1, hi).items():
                    out.setdefault(a | b | here, (ta, tb))
        return out

    return tips, qs, interval(1, len(tips) - 1)


def check_pattern(n, qs, pattern, twice_cherry_score=0):
    lookup = {}
    for qi, quartet in enumerate(qs):
        code = (pattern >> (3 * qi)) & 7
        assert code in (1, 4, 5), (quartet, code)
        a, b, c, d = quartet
        splits = []
        if code & 1:
            splits.append({a, b})
        if code & 4:
            splits.append({a, d})
        lookup[quartet] = splits
    checked = 0
    for p, q in combinations(range(n), 2):
        def entry(x, y):
            if x == y or {x, y} == {p, q}:
                return 0
            if {x, y} & {p, q}:
                return 1
            splits = lookup[tuple(sorted((x, y, p, q)))]
            separated = sum((x in s) != (y in s) for s in splits)
            if len(splits) == 1 and separated == 0:
                return twice_cherry_score
            return 2 * separated // len(splits)
        for i, j in combinations(range(n), 2):
            a, b, c, d = i, (i + 1) % n, j, (j + 1) % n
            alpha = entry(a, c) + entry(b, d) - entry(a, d) - entry(b, c)
            checked += 1
            if alpha < 0:
                return checked, {"anchors": [p, q], "boundary_indices": [i, j], "alpha": alpha,
                                 "quartets": [{"taxa": list(Q), "code": (pattern >> (3 * idx)) & 7}
                                              for idx, Q in enumerate(qs)]}
    return checked, None


def scan():
    report = {"status": "representation_screen_only", "rows": [], "failure": None, "modified_failure": None,
              "warning": "Completeness of adjacent-pair representation for source bloblets and six-taxon compression requires mathematical review."}
    for n in range(3, 7):
        seen = set()
        row = {"taxa": n, "duplication_masks": 0, "plane_trees_represented": 0,
               "distinct_quartet_systems": 0, "anchor_coefficients": 0, "modified_anchor_coefficients": 0}
        for duplicated in range(1 << n):
            tips, qs, patterns = systems(n, duplicated)
            m = len(tips) - 2
            row["plane_trees_represented"] += comb(2 * m, m) // (m + 1)
            row["duplication_masks"] += 1
            for pattern, tree in patterns.items():
                if pattern in seen:
                    continue
                seen.add(pattern)
                checked, failure = check_pattern(n, qs, pattern)
                row["anchor_coefficients"] += checked
                modified_checked, modified_failure = check_pattern(n, qs, pattern, 1)
                row["modified_anchor_coefficients"] += modified_checked
                if modified_failure and report["modified_failure"] is None:
                    report["modified_failure"] = {"taxa": n, "duplicated_mask": duplicated, "expanded_tip_labels": tips,
                                                   "rooted_plane_tree": [0, tree], "pattern": pattern, **modified_failure}
                if failure:
                    failure.update({"taxa": n, "duplicated_mask": duplicated, "expanded_tip_labels": tips,
                                    "rooted_plane_tree": [0, tree], "pattern": pattern})
                    row["distinct_quartet_systems"] = len(seen)
                    report["rows"].append(row)
                    report["failure"] = failure
                    return report
        row["distinct_quartet_systems"] = len(seen)
        report["rows"].append(row)
    return report


if __name__ == "__main__":
    result = scan()
    Path(__file__).with_name("all-level-screen.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
