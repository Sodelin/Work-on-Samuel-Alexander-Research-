"""Exact inequalities for universal anchor positivity in the paired-tip representation.

This criterion is sufficient for circularity. It need not characterize every
parameter making the unit-mass distance circular.
"""
import json
from itertools import combinations
from functools import reduce
from math import gcd
from pathlib import Path
from all_level_screen import systems


def derive():
    inequalities = {}
    for n in range(3, 7):
        seen = set()
        for mask in range(1 << n):
            _, qs, patterns = systems(n, mask)
            for pattern in patterns:
                if pattern in seen:
                    continue
                seen.add(pattern)
                qcodes = {q: (pattern >> (3 * i)) & 7 for i, q in enumerate(qs)}
                for p, q in combinations(range(n), 2):
                    def vec(x, y):
                        out = [0] * 5
                        if x == y or {x, y} == {p, q}:
                            return out
                        if {x, y} & {p, q}:
                            out[0] = 1
                            return out
                        Q = tuple(sorted((x, y, p, q)))
                        a, b, c, d = Q
                        code = qcodes[Q]
                        splits = ([{a, b}] if code & 1 else []) + ([{a, d}] if code & 4 else [])
                        separated = sum((x in s) != (y in s) for s in splits)
                        ix = (1 + separated) if len(splits) == 1 else (3 if separated == 1 else 4)
                        out[ix] = 2
                        return out
                    for i, j in combinations(range(n), 2):
                        v1, v2, v3, v4 = vec(i, j), vec((i+1) % n, (j+1) % n), vec(i, (j+1) % n), vec((i+1) % n, j)
                        raw = tuple(a+b-c-d for a, b, c, d in zip(v1, v2, v3, v4))
                        divisor = reduce(gcd, map(abs, raw))
                        if divisor == 0:
                            continue
                        normal = tuple(v // divisor for v in raw)
                        inequalities.setdefault(normal, {"taxa": n, "duplication_mask": mask,
                                                         "pattern": pattern, "anchors": [p, q], "gaps": [i, j]})
    return {"variables": ["constant_1", "rho_c", "rho_s", "rho_a", "rho_o"],
            "interpretation": "dot(row,[1,c,s,a,o]) >= 0; scores additionally nonnegative",
            "scope": "Necessary and sufficient for every anchor coefficient in the paired-tip representation; sufficiency for source bloblet circularity uses ALL-LEVEL-PROOF.md.",
            "inequalities": [{"row": row, "witness": witness} for row, witness in sorted(inequalities.items())]}


if __name__ == "__main__":
    result = derive()
    Path(__file__).with_name("parameter-domain.json").write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"inequality_count": len(result["inequalities"]), "rows": [x["row"] for x in result["inequalities"]]}, indent=2))
