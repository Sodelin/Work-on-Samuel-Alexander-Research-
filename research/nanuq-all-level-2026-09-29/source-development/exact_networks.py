"""Exact finite controls for the NANUQ multi-blob conjecture.

Only the Python standard library is used. Graphs have no parallel edges in this
initial family. Rotation systems certify planarity and a common outer leaf face.
The search is finite evidence, not a proof of the conjecture.
"""
from __future__ import annotations

import argparse
from collections import deque
from fractions import Fraction as F
from itertools import combinations, product
import json
from math import atan2
from pathlib import Path


def edge(a, b):
    return tuple(sorted((a, b)))


def adjacency(edges):
    adj = {}
    for a, b in edges:
        adj.setdefault(a, set()).add(b)
        adj.setdefault(b, set()).add(a)
    return adj


def reachable(adj, start, forbidden=None):
    seen = {start}
    todo = [start]
    while todo:
        a = todo.pop()
        for b in adj[a]:
            if edge(a, b) == forbidden or b in seen:
                continue
            seen.add(b)
            todo.append(b)
    return seen


class Net:
    def __init__(self, edges, leaves, hybrids, root, rotation, name):
        self.edges = set(edges)
        self.leaves = set(leaves)
        self.hybrids = {h: tuple(ps) for h, ps in hybrids.items()}
        self.root = root
        self.rotation = {v: list(ns) for v, ns in rotation.items()}
        self.name = name

    def validate(self):
        adj = adjacency(self.edges)
        assert reachable(adj, self.root) == set(adj)
        assert all(len(adj[v]) == (1 if v in self.leaves else 2 if v == self.root else 3)
                   for v in adj)
        assert set(self.rotation) == set(adj)
        assert all(set(self.rotation[v]) == ns and len(self.rotation[v]) == len(ns)
                   for v, ns in adj.items())
        # Combinatorial embedding certificate: every directed edge is in a face,
        # Euler characteristic is 2, and some face contains all labelled leaves.
        darts = {(u, v) for u in adj for v in adj[u]}
        faces = []
        while darts:
            start = min(darts)
            a, b = start
            face = []
            while True:
                assert (a, b) in darts
                darts.remove((a, b))
                face.append(a)
                rs = self.rotation[b]
                a, b = b, rs[(rs.index(a) + 1) % len(rs)]
                if (a, b) == start:
                    break
            faces.append(face)
        assert len(adj) - len(self.edges) + len(faces) == 2
        outer = [face for face in faces if self.leaves <= set(face)]
        assert outer, 'no face contains all labelled leaves'
        circular = [v for v in outer[0] if v in self.leaves]
        assert len(circular) == len(self.leaves)
        # Ordinary edges form a forest oriented from the original root or one
        # hybrid vertex per component. Hybrid incoming arrows remain fixed.
        incoming = {edge(p, h) for h, ps in self.hybrids.items() for p in ps}
        assert incoming <= self.edges
        forest = {v: set() for v in adj}
        for a, b in self.edges - incoming:
            forest[a].add(b)
            forest[b].add(a)
        oriented = {(p, h) for h, ps in self.hybrids.items() for p in ps}
        remaining = set(adj)
        while remaining:
            component = reachable(forest, min(remaining))
            remaining -= component
            roots = component & ({self.root} | set(self.hybrids))
            assert len(roots) == 1, ('invalid rooted partner', roots)
            r = next(iter(roots))
            seen = {r}
            todo = [r]
            while todo:
                a = todo.pop()
                for b in forest[a]:
                    if b in seen:
                        continue
                    seen.add(b)
                    oriented.add((a, b))
                    todo.append(b)
            assert sum(len(forest[v]) for v in component) // 2 == len(component) - 1
        parents = {v: set() for v in adj}
        children = {v: set() for v in adj}
        for a, b in oriented:
            parents[b].add(a)
            children[a].add(b)
        for v in adj:
            expected = (0, 2) if v == self.root else (1, 0) if v in self.leaves else (2, 1) if v in self.hybrids else (1, 2)
            assert (len(parents[v]), len(children[v])) == expected
        indeg = {v: len(parents[v]) for v in adj}
        todo = deque([self.root])
        topo = []
        while todo:
            v = todo.popleft()
            topo.append(v)
            for w in children[v]:
                indeg[w] -= 1
                if indeg[w] == 0:
                    todo.append(w)
        assert len(topo) == len(adj), 'directed cycle'
        dominators = {}
        for v in topo:
            dominators[v] = {v} if v == self.root else {v} | set.intersection(*(dominators[p] for p in parents[v]))
        assert set.intersection(*(dominators[x] for x in self.leaves)) == {self.root}, 'root not LSA'
        bridges = {e for e in self.edges if e[1] not in reachable(adj, e[0], e)}
        blobadj = {v: ns.copy() for v, ns in adj.items()}
        for a, b in bridges:
            blobadj[a].remove(b)
            blobadj[b].remove(a)
        remaining = set(adj)
        levels = []
        while remaining:
            component = reachable(blobadj, min(remaining))
            remaining -= component
            levels.append(len(component & set(self.hybrids)))
        assert max(levels) <= 2
        # In this binary setting, a hybrid is galled iff it is a blob articulation.
        assert all(any(edge(h, c) in bridges for c in children[h]) for h in self.hybrids)
        return {'circular_order': circular, 'vertices': len(adj), 'edges': len(self.edges),
                'leaves': len(self.leaves), 'hybrids': len(self.hybrids),
                'blob_hybrid_counts': sorted(levels, reverse=True), 'faces': len(faces)}


def theta(counts=(1, 1, 1, 1), prefix='n'):
    """Four arm counts are a1,b1,a2,b2; all are nonnegative integers."""
    r, u, v, h1, h2 = (prefix + x for x in ('r', 'u', 'v', 'h1', 'h2'))
    coords = {r: (0, 0), u: (-1, 0), v: (1, 0), h1: (0, 1), h2: (0, -1)}
    edges = {edge(r, u), edge(r, v)}
    leaves = set()
    ps = {h1: [], h2: []}
    for label, start, end, k, normal in zip(('a1', 'b1', 'a2', 'b2'), (u, v, u, v), (h1, h1, h2, h2), counts, ((-1, 1), (1, 1), (-1, -1), (1, -1))):
        previous = start
        x0, y0 = coords[start]
        x1, y1 = coords[end]
        for j in range(k):
            node = prefix + label + 'v' + str(j)
            leaf = prefix + label + 'l' + str(j)
            t = (j + 1) / (k + 1)
            coords[node] = (x0 + t * (x1 - x0), y0 + t * (y1 - y0))
            coords[leaf] = (coords[node][0] + normal[0] / 8, coords[node][1] + normal[1] / 8)
            edges.update((edge(previous, node), edge(node, leaf)))
            leaves.add(leaf)
            previous = node
        edges.add(edge(previous, end))
        ps[end].append(previous)
    for i, h in enumerate((h1, h2), 1):
        leaf = prefix + 'c' + str(i)
        leaves.add(leaf)
        coords[leaf] = (0, 1.25 if i == 1 else -1.25)
        edges.add(edge(h, leaf))
    adj = adjacency(edges)
    rotation = {a: sorted(ns, key=lambda b: atan2(coords[b][1] - coords[a][1], coords[b][0] - coords[a][0])) for a, ns in adj.items()}
    return Net(edges, leaves, ps, r, rotation, 'theta' + str(tuple(counts)))


def cherry_at(net, leaf, prefix):
    """Replace one pendant leaf by an ordinary binary cherry."""
    adj = adjacency(net.edges)
    p = next(iter(adj[leaf]))
    s, x, y = prefix + 's', prefix + 'x', prefix + 'y'
    edges = net.edges - {edge(p, leaf)} | {edge(p, s), edge(s, x), edge(s, y)}
    rot = {v: ns.copy() for v, ns in net.rotation.items() if v != leaf}
    rot[p][rot[p].index(leaf)] = s
    rot[s], rot[x], rot[y] = [p, x, y], [s], [s]
    return Net(edges, net.leaves - {leaf} | {x, y}, net.hybrids, net.root, rot, net.name + '+cherry')


def graft(parent, leaf, child, port):
    """Join two leaf ports, suppressing the child's original degree-two root.

    The child port must permit a rooted partner from this attachment. validate()
    checks this rather than presuming that every hybrid-child port is legal.
    """
    assert not (set(parent.rotation) & set(child.rotation))
    pedges = parent.edges.copy()
    cedges = child.edges.copy()
    rot = {v: ns.copy() for v, ns in (parent.rotation | child.rotation).items()}
    a, b = rot[child.root]
    cedges -= {edge(a, child.root), edge(b, child.root)}
    cedges.add(edge(a, b))
    rot[a][rot[a].index(child.root)] = b
    rot[b][rot[b].index(child.root)] = a
    del rot[child.root]
    p, q = rot[leaf][0], rot[port][0]
    edges = pedges | cedges
    edges -= {edge(p, leaf), edge(q, port)}
    edges.add(edge(p, q))
    rot[p][rot[p].index(leaf)] = q
    rot[q][rot[q].index(port)] = p
    del rot[leaf], rot[port]
    return Net(edges, parent.leaves - {leaf} | child.leaves - {port}, parent.hybrids | child.hybrids,
               parent.root, rot, parent.name + '+graft+' + child.name)


def canonical_split(side, leaves):
    a, b = tuple(sorted(side)), tuple(sorted(set(leaves) - set(side)))
    return min(a, b)


def simplify_tree(edges, leaves):
    adj = adjacency(edges)
    changed = True
    while changed:
        changed = False
        for v in list(adj):
            if v in leaves or len(adj[v]) > 2:
                continue
            ns = list(adj.pop(v))
            for u in ns:
                adj[u].remove(v)
            if len(ns) == 2:
                a, b = ns
                adj[a].add(b)
                adj[b].add(a)
            changed = True
    assert set(leaves) <= set(adj)
    assert all(len(ns) == (1 if v in leaves else 3) for v, ns in adj.items())
    out = {edge(a, b) for a, ns in adj.items() for b in ns}
    assert len(out) == len(adj) - 1
    assert reachable(adj, min(adj)) == set(adj)
    return out


def tree_splits(edges, leaves):
    adj = adjacency(edges)
    return frozenset(canonical_split(reachable(adj, a, (a, b)) & set(leaves), leaves) for a, b in edges)


def displayed_splits(net):
    out = []
    hybrids = sorted(net.hybrids)
    for choices in product((0, 1), repeat=len(hybrids)):
        es = net.edges.copy()
        for h, choice in zip(hybrids, choices):
            es.remove(edge(net.hybrids[h][1 - choice], h))
        out.append(tree_splits(simplify_tree(es, net.leaves), net.leaves))
    return out


def quartet_system(net):
    trees = displayed_splits(net)
    qs = {}
    for q in combinations(sorted(net.leaves), 4):
        qset = set(q)
        displayed = set()
        for ts in trees:
            splits = {canonical_split(set(s) & qset, qset) for s in ts if len(set(s) & qset) == 2}
            assert len(splits) == 1
            displayed |= splits
        qs[q] = displayed
    return qs, trees


def rho(qs, x, y, z, w):
    splits = qs[tuple(sorted((x, y, z, w)))]
    return F(sum((x in s) != (y in s) for s in splits), len(splits))


def distance(qs, order, masses=None):
    masses = masses or {x: 1 for x in order}
    d = {(x, x): F(0) for x in order}
    for x, y in combinations(order, 2):
        rest = [z for z in order if z not in (x, y)]
        value = 2 * sum((masses[z] * masses[w] * rho(qs, x, y, z, w) for z, w in combinations(rest, 2)), F(0))
        value += (masses[x] + masses[y]) * sum(masses[z] for z in rest)
        d[x, y] = d[y, x] = value
    return d


def coefficients(d, order):
    n = len(order)
    out = []
    for i, j in combinations(range(n), 2):
        a, b, c, e = order[i], order[(i+1) % n], order[j], order[(j+1) % n]
        split = canonical_split(order[i+1:j+1], order)
        out.append((split, d[a, c] + d[b, e] - d[a, e] - d[b, c], (i, j)))
    return out


def anchor_distance(qs, order, p, q):
    d = {(x, x): F(0) for x in order}
    for x, y in combinations(order, 2):
        value = F(0) if {x, y} == {p, q} else F(1) if {x, y} & {p, q} else 2*rho(qs, x, y, p, q)
        d[x, y] = d[y, x] = value
    return d


def local_decomposition(net, order):
    """Sum weighted local blob metrics lifted through their pendant components.

    Isolated non-leaf vertices count as blobs. A two-port blob contributes zero.
    The identity is checked against independently computed global quartets.
    """
    adj = adjacency(net.edges)
    bridges = {e for e in net.edges if e[1] not in reachable(adj, e[0], e)}
    blobadj = {v: ns.copy() for v, ns in adj.items()}
    for a, b in bridges:
        blobadj[a].remove(b)
        blobadj[b].remove(a)
    remaining = set(adj)
    total = {(x, y): F(0) for x in order for y in order}
    summaries = []
    while remaining:
        component = reachable(blobadj, min(remaining))
        remaining -= component
        if component <= net.leaves:
            continue
        es = {e for e in net.edges if set(e) <= component}
        ports, masses, projection = [], {}, {}
        for a, b in sorted(bridges):
            if (a in component) == (b in component):
                continue
            u, v = (a, b) if a in component else (b, a)
            port = 'PORT:' + u + ':' + v
            taxa = reachable(adj, v, edge(u, v)) & net.leaves
            assert taxa
            ports.append(port)
            masses[port] = len(taxa)
            es.add(edge(u, port))
            for x in taxa:
                assert x not in projection
                projection[x] = port
        assert set(projection) == net.leaves
        assert len(ports) >= 2
        local = Net(es, ports, {h:ps for h,ps in net.hybrids.items() if h in component}, None, {}, 'local')
        qs, trees = quartet_system(local)
        ld = distance(qs, ports, masses)
        for x in order:
            for y in order:
                total[x,y] += ld[projection[x], projection[y]]
        summaries.append({'ports': len(ports), 'hybrids': len(local.hybrids), 'masses': sorted(masses.values())})
    return total, summaries


def check(net, anchors=False):
    cert = net.validate()
    order = cert['circular_order']
    qs, trees = quartet_system(net)
    d = distance(qs, order)
    decomposed, blobs = local_decomposition(net, order)
    assert decomposed == d, ('blob metric decomposition failed', net.name)
    cs = coefficients(d, order)
    expected = set().union(*trees)
    positive = {s for s, a, ij in cs if a > 0}
    assert positive == expected, (net.name, 'support failure', positive ^ expected)
    assert all(a >= 0 for s, a, ij in cs), (net.name, 'negative coefficient')
    for x, y, z in combinations(order, 3):
        assert d[x, y] <= d[x, z]+d[z, y]
        assert d[x, z] <= d[x, y]+d[y, z]
        assert d[y, z] <= d[y, x]+d[x, z]
    negatives = []
    if anchors:
        for p, q in combinations(order, 2):
            ad = anchor_distance(qs, order, p, q)
            for s, a, ij in coefficients(ad, order):
                if a < 0:
                    negatives.append({'anchors': [p, q], 'split': s, 'coefficient': str(a), 'indices': ij})
    return {'name': net.name, **cert, 'switchings': len(trees), 'distinct_trees': len(set(trees)),
            'quartets': len(qs), 'displayed_splits': len(expected), 'minimum_coefficient': str(min(a for s,a,ij in cs)),
            'anchor_coefficient_checks': (len(order)*(len(order)-1)//2)**2 if anchors else 0,
            'weighted_blob_decomposition': blobs,
            'anchor_negative_count': len(negatives), 'anchor_negative_examples': negatives[:4]}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--output', type=Path, required=True)
    ap.add_argument('--max-arm', type=int, default=2)
    ap.add_argument('--max-total-arm', type=int)
    args = ap.parse_args()
    rows = []
    for counts in product(range(args.max_arm + 1), repeat=4):
        if sum(counts) < (1 if args.max_total_arm is not None else 2):
            continue
        if args.max_total_arm is not None and sum(counts) > args.max_total_arm:
            continue
        row = check(theta(counts), anchors=True)
        rows.append(row)
        if row['anchor_negative_count']:
            print('NEGATIVE ANCHOR', json.dumps(row), flush=True)
    template_count = len(rows)
    core = theta()
    for k, leaf in enumerate(sorted(core.leaves)):
        rows.append(check(cherry_at(core, leaf, 'c'+str(k)), anchors=False))
        child = theta(prefix='child'+str(k))
        port = 'child'+str(k)+'a1l0'
        rows.append(check(graft(core, leaf, child, port), anchors=False))
    receipt = {'status': 'PASS_UNIT_METRICS', 'scope': 'Finite exact constructed-family search; no universal theorem',
               'cases': len(rows), 'max_arm': args.max_arm, 'max_total_arm': args.max_total_arm,
               'completed_template_sweep': True, 'template_count': template_count,
               'anchor_status': 'PASS' if all(r['anchor_negative_count'] == 0 for r in rows) else 'COUNTEREXAMPLE',
               'anchor_coefficient_checks': sum(r['anchor_coefficient_checks'] for r in rows), 'results': rows}
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(receipt, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': receipt['status'], 'cases': len(rows), 'negative_anchor_cases': sum(r['anchor_negative_count'] > 0 for r in rows), 'output': str(args.output)}), flush=True)


if __name__ == '__main__':
    main()
