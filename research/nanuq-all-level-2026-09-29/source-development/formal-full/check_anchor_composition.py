"""Exact finite test of the stronger, per-anchor blob identity.

This is exploratory evidence, not a Lean certificate or an unbounded proof.
The frozen fixtures and original evaluator are read without modification.
"""
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import exact_networks as en


def local_blobs(net):
    adj = en.adjacency(net.edges)
    bridges = {e for e in net.edges if e[1] not in en.reachable(adj, e[0], e)}
    blobadj = {v: ns.copy() for v, ns in adj.items()}
    for a, b in bridges:
        blobadj[a].remove(b)
        blobadj[b].remove(a)
    remaining = set(adj)
    result = []
    while remaining:
        component = en.reachable(blobadj, min(remaining))
        remaining -= component
        if component <= net.leaves:
            continue
        es = {e for e in net.edges if set(e) <= component}
        ports, projection = [], {}
        for a, b in sorted(bridges):
            if (a in component) == (b in component):
                continue
            u, v = (a, b) if a in component else (b, a)
            port = 'PORT:' + u + ':' + v
            taxa = en.reachable(adj, v, en.edge(u, v)) & net.leaves
            assert taxa
            ports.append(port)
            es.add(en.edge(u, port))
            for x in taxa:
                assert x not in projection
                projection[x] = port
        assert set(projection) == net.leaves
        local = en.Net(es, ports,
                       {h: ps for h, ps in net.hybrids.items() if h in component},
                       None, {}, 'local')
        qs, _ = en.quartet_system(local)
        anchors = {frozenset((p, q)): en.anchor_distance(qs, ports, p, q)
                   for p, q in combinations(ports, 2)}
        result.append((projection, anchors))
    return result


def main():
    fixtures = json.loads((HERE.parent / 'composition-controls.json').read_text())
    rows = []
    total = 0
    for fixture in fixtures['results']:
        order = fixture['circular_order']
        net = en.Net([tuple(e) for e in fixture['edge_list']], order,
                     fixture['hybrid_parents'], None, {}, fixture['name'])
        qs, _ = en.quartet_system(net)
        locals_ = local_blobs(net)
        checks = 0
        for p, q in combinations(order, 2):
            global_anchor = en.anchor_distance(qs, order, p, q)
            for x in order:
                for y in order:
                    composed = sum((anchor[frozenset((proj[p], proj[q]))]
                                    [proj[x], proj[y]]
                                    for proj, anchor in locals_ if proj[p] != proj[q]),
                                   Fraction(0))
                    assert global_anchor[x, y] == composed, (
                        net.name, p, q, x, y, global_anchor[x, y], composed)
                    checks += 1
        total += checks
        rows.append({'name': net.name, 'leaves': len(order), 'blobs': len(locals_),
                     'anchor_entry_equalities': checks})
    receipt = {'status': 'PASS', 'scope': 'Finite exploratory evidence only',
               'identity': 'M_N^(p,q)(x,y) = sum_B [pi_B(p) != pi_B(q)] '
                           'M_B^(pi_B(p),pi_B(q))(pi_B(x),pi_B(y))',
               'networks': len(rows), 'anchor_entry_equalities': total, 'results': rows}
    (HERE / 'anchor-composition-control.json').write_text(json.dumps(receipt, indent=2) + '\n')
    print(json.dumps({k: v for k, v in receipt.items() if k != 'results'}))


if __name__ == '__main__':
    main()
