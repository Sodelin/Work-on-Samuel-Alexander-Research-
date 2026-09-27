"""Exact finite controls for RECOVERY-THEOREM.md; not a general proof."""
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json


def components(families, vectors, blocks):
    n = len(families)
    parent = list(range(n))
    def root(x):
        while parent[x] != x:
            parent[x] = parent[parent[x]]
            x = parent[x]
        return x
    # Actual observable symbols are (family, selected parent) at each block.
    observed = [[(families[c], (vectors[c] >> b) & 1)
                 for b in range(blocks)] for c in range(n)]
    for a in range(n):
        for b in range(a):
            if any(observed[a][j] == observed[b][j] for j in range(blocks)):
                parent[root(a)] = root(b)
    return frozenset(frozenset(c for c in range(n) if root(c) == r)
                     for r in {root(c) for c in range(n)})


def expected_partition(families):
    return frozenset(frozenset(c for c, f in enumerate(families) if f == target)
                     for target in set(families))


def failure(m, blocks):
    assert m >= 1 and blocks >= 1
    return Fraction(2 ** (m - 1) - 1, 2 ** (blocks * (m - 1)))


rows = []
assignments = 0
for m in range(1, 7):
    for blocks in range(1, 5):
        if m * blocks > 16:
            continue
        families = (0,) * m
        truth = expected_partition(families)
        recovered = 0
        mask = 2 ** blocks - 1
        for vectors in product(range(2 ** blocks), repeat=m):
            found = components(families, vectors, blocks)
            success = found == truth
            seen = set(vectors)
            complementary_pair = (len(seen) == 2 and
                                  {v ^ mask for v in seen} == seen)
            assert success == (not complementary_pair)
            recovered += success
        total = 2 ** (m * blocks)
        rate = Fraction(recovered, total)
        assert rate == 1 - failure(m, blocks)
        assignments += total
        rows.append({'family_size': m, 'blocks': blocks, 'assignments': total,
                     'exact_success': str(rate)})

multi = []
for sizes in [(1, 3), (2, 2), (3, 3)]:
    families = tuple(f for f, m in enumerate(sizes) for _ in range(m))
    truth = expected_partition(families)
    for blocks in [1, 2]:
        recovered = 0
        for vectors in product(range(2 ** blocks), repeat=len(families)):
            found = components(families, vectors, blocks)
            assert all(len({families[c] for c in group}) == 1 for group in found)
            recovered += found == truth
        predicted = Fraction(1)
        for m in sizes:
            predicted *= 1 - failure(m, blocks)
        total = 2 ** (len(families) * blocks)
        rate = Fraction(recovered, total)
        assert rate == predicted
        assignments += total
        multi.append({'sizes': sizes, 'blocks': blocks, 'assignments': total,
                      'exact_success': str(rate)})

monotone = 0
for m in range(1, 5):
    families = (0,) * m
    for blocks in [1, 2]:
        for vectors in product(range(2 ** blocks), repeat=m):
            old = components(families, vectors, blocks)
            for extra in product([0, 1], repeat=m):
                extended = tuple(v | (bit << blocks) for v, bit in zip(vectors, extra))
                new = components(families, extended, blocks + 1)
                assert all(any(c <= d for d in new) for c in old)
                monotone += 1

correlated = []
for m in [2, 3, 4, 5]:
    families = (0,) * m
    truth = expected_partition(families)
    for blocks in [1, 2, 5]:
        mask = 2 ** blocks - 1
        recovered = sum(components(families, tuple(bit * mask for bit in bits), blocks)
                        == truth for bits in product([0, 1], repeat=m))
        rate = Fraction(recovered, 2 ** m)
        assert rate == Fraction(1, 2 ** (m - 1))
        correlated.append({'family_size': m, 'blocks': blocks, 'success': str(rate)})

for blocks in range(1, 6):
    for families in [(0, 0), (0, 1)]:
        together = sum(len(components(families, pair, blocks)) == 1
                       for pair in product(range(2 ** blocks), repeat=2))
        predicted = 1 - Fraction(1, 2 ** blocks) if families[0] == families[1] else 0
        assert Fraction(together, 2 ** (2 * blocks)) == predicted

for families in [(0,), (0, 0), (0, 1), (0, 0, 1)]:
    found = components(families, (0,) * len(families), 0)
    assert (found == expected_partition(families)) == (len(set(families)) == len(families))

receipt = {
    'status': 'PASS_FINITE_EXHAUSTIVE_CONTROLS_NOT_GENERAL_PROOF_OR_LEAN',
    'one_family_cases': rows, 'multiple_family_cases': multi,
    'enumerated_probability_assignments': assignments,
    'append_block_monotonicity_cases': monotone,
    'correlated_block_controls': correlated,
    'pair_event_identity': 'PASS_B_1_TO_5',
    'zero_block_boundary': 'PASS',
    'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
}
Path(__file__).with_name('CHECK-RESULT.json').write_text(
    json.dumps(receipt, indent=2) + '\n', encoding='utf-8')
print(json.dumps({k: v for k, v in receipt.items() if k not in
                 {'one_family_cases', 'multiple_family_cases', 'correlated_block_controls'}}, indent=2))
