"""Direct level-three candidate screen. Exhaustive source coverage is unproved.

The two underlying bridgeless cubic four-vertex multigraphs are K4 and a
four-cycle with opposite edges doubled. Chosen outer-face hybrid placements
give six and seven ordinary leaf segments. All concrete inputs are checked by
the inherited connectivity, binary, rooted-DAG, LSA, level and rotation tests.
"""
import argparse
import hashlib
import json
from fractions import Fraction as F
from itertools import combinations, product
from math import atan2
from pathlib import Path
import level3_backend as ex


def make_net(kind, counts):
    if kind == "k4":
        coords = {"a": (-2, -1), "b": (2, -1), "c": (0, 2), "d": (0, 0),
                  "h1": (0, -1), "h2": (1, .5), "h3": (-1, .5), "r": (-1, -.5)}
        cycle = ("a", "h1", "b", "h2", "c", "h3")
        normals = ((0, -1), (0, -1), (1, 1), (1, 1), (-1, 1), (-1, 1))
        edges = {ex.edge("d", "r"), ex.edge("r", "a"), ex.edge("d", "b"), ex.edge("d", "c")}
        hybrid_normals = {"h1": (0, -1), "h2": (1, 1), "h3": (-1, 1)}
    else:
        coords = {"a": (-2, 1), "b": (2, 1), "c": (2, -1), "d": (-2, -1),
                  "h1": (0, 2), "h2": (3, 0), "h3": (0, -2), "r": (0, 1)}
        cycle = ("a", "h1", "b", "h2", "c", "h3", "d")
        normals = ((-1, 1), (1, 1), (1, 1), (1, -1), (1, -1), (-1, -1), (-1, 0))
        edges = {ex.edge("a", "r"), ex.edge("r", "b"), ex.edge("c", "d")}
        hybrid_normals = {"h1": (0, 1), "h2": (1, 0), "h3": (0, -1)}
    assert len(counts) == len(cycle)
    leaves = set()
    for arm, start in enumerate(cycle):
        end = cycle[(arm + 1) % len(cycle)]
        x0, y0 = coords[start]
        x1, y1 = coords[end]
        previous = start
        nx, ny = normals[arm]
        for j in range(counts[arm]):
            node, leaf = f"v{arm}_{j}", f"l{arm}_{j}"
            t = (j + 1) / (counts[arm] + 1)
            coords[node] = (x0 + t * (x1 - x0), y0 + t * (y1 - y0))
            coords[leaf] = (coords[node][0] + nx / 8, coords[node][1] + ny / 8)
            edges.update((ex.edge(previous, node), ex.edge(node, leaf)))
            leaves.add(leaf)
            previous = node
        edges.add(ex.edge(previous, end))
    hybrids = {}
    for h, (nx, ny) in hybrid_normals.items():
        hybrids[h] = tuple(sorted(ex.adjacency(edges)[h]))
        leaf = "taxon_" + h
        coords[leaf] = (coords[h][0] + nx / 4, coords[h][1] + ny / 4)
        edges.add(ex.edge(h, leaf))
        leaves.add(leaf)
    adj = ex.adjacency(edges)
    rotation = {v: sorted(ns, key=lambda w: atan2(coords[w][1] - coords[v][1], coords[w][0] - coords[v][0]))
                for v, ns in adj.items()}
    return ex.Net(edges, leaves, hybrids, "r", rotation, kind + str(counts))


def weak_compositions(total, parts):
    if parts == 1:
        yield (total,)
    else:
        for head in range(total + 1):
            for tail in weak_compositions(total - head, parts - 1):
                yield (head,) + tail


def core_inventory():
    pairs = list(combinations(range(4), 2))
    representatives = set()
    from itertools import permutations
    for mult in product(range(4), repeat=6):
        if any(sum(m for e, m in zip(pairs, mult) if v in e) != 3 for v in range(4)):
            continue
        expanded = [e for e, m in zip(pairs, mult) for _ in range(m)]
        def connected(es):
            seen = {0}
            for _ in range(4):
                seen |= {v for a, b in es if a in seen or b in seen for v in (a, b)}
            return len(seen) == 4
        if not connected(expanded) or any(not connected(expanded[:i] + expanded[i+1:]) for i in range(6)):
            continue
        variants = []
        for p in permutations(range(4)):
            renamed = [tuple(sorted((p[a], p[b]))) for a, b in expanded]
            variants.append(tuple(renamed.count(e) for e in pairs))
        representatives.add(min(variants))
    return {"vertex_pairs": pairs, "nonisomorphic_bridgeless_cubic_cores": sorted(representatives)}


def scan(max_total):
    result = {"status": "bounded_candidate_family_screen", "max_ordinary_leaves": max_total,
              "core_inventory": core_inventory(), "families": [], "unit_failure": None, "anchor_failure": None,
              "coverage_warning": "These two explicit families have not yet been proved to exhaust the source class."}
    for kind, arms in (("k4", 6), ("double_square", 7)):
        row = {"kind": kind, "templates": 0, "unit_coefficients": 0, "anchor_coefficients": 0,
               "unit_support_mismatches": 0, "max_leaves": 0}
        for total in range(max_total + 1):
            for counts in weak_compositions(total, arms):
                net = make_net(kind, counts)
                admission = net.validate()
                assert admission["blob_hybrid_counts"][0] == 3
                order = admission["circular_order"]
                qs, trees = ex.quartet_system(net)
                d = ex.distance(qs, order)
                cs = ex.coefficients(d, order)
                row["templates"] += 1
                row["max_leaves"] = max(row["max_leaves"], len(order))
                row["unit_coefficients"] += len(cs)
                support = {s for s, a, _ in cs if a > 0}
                row["unit_support_mismatches"] += support != set().union(*trees)
                bad = [(s, str(a), ij) for s, a, ij in cs if a < 0]
                if bad:
                    result["unit_failure"] = {"kind": kind, "counts": counts, "order": order, "negative": bad}
                    result["families"].append(row)
                    return result
                for p, q in combinations(order, 2):
                    acs = ex.coefficients(ex.anchor_distance(qs, order, p, q), order)
                    row["anchor_coefficients"] += len(acs)
                    bad = [(s, str(a), ij) for s, a, ij in acs if a < 0]
                    if bad:
                        result["anchor_failure"] = {"kind": kind, "counts": counts, "order": order,
                                                    "anchors": [p, q], "negative": bad}
                        result["families"].append(row)
                        return result
        result["families"].append(row)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-total", type=int, default=3)
    args = parser.parse_args()
    result = scan(args.max_total)
    result["backend_sha256"] = hashlib.sha256(Path(ex.__file__).read_bytes()).hexdigest()
    target = Path(__file__).with_name(f"level3-screen-{args.max_total}.json")
    target.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
