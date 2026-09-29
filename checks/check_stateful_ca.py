"""Exact local and finite-orbit checks for the synthetic proposal-10 rule."""

from itertools import product

DEAD, R, L = 0, 1, 2
OFFSETS = {
    "W": (-1, 0), "NW": (-1, 1), "SW": (-1, -1),
    "E": (1, 0), "NE": (1, 1), "SE": (1, -1),
}
NAMES = tuple(OFFSETS)


def output(q):
    if q["W"] == R and (q["NW"] == R or q["SW"] == R):
        return L
    if q["E"] == L and (q["NE"] == L or q["SE"] == L):
        return R
    return DEAD


def step(cells):
    candidates = {
        (x - dx, y - dy)
        for (x, y) in cells
        for dx, dy in OFFSETS.values()
    }
    result = {}
    for x, y in candidates:
        q = {name: cells.get((x + dx, y + dy), DEAD)
             for name, (dx, dy) in OFFSETS.items()}
        state = output(q)
        if state:
            result[x, y] = state
    return result


def audit():
    live_rows = {R: 0, L: 0}
    for values in product((DEAD, R, L), repeat=len(NAMES)):
        q = dict(zip(NAMES, values))
        target = output(q)
        if target == DEAD:
            continue
        live_rows[target] += 1
        if target == L:
            assert q["W"] == R and (q["NW"] == R or q["SW"] == R)
            parents = ("W", "NW" if q["NW"] == R else "SW")
        else:
            assert q["E"] == L and (q["NE"] == L or q["SE"] == L)
            parents = ("E", "NE" if q["NE"] == L else "SE")
        assert len(set(parents)) == 2
        for name in parents:
            source = q[name]
            dx, _ = OFFSETS[name]
            horizontal_step = -dx
            h = {R: 1, L: 0}
            assert horizontal_step <= h[source] - h[target]

    cells = {(0, 0): R, (0, 1): R}
    orbit = []
    for _ in range(8):
        orbit.append(tuple(sorted(cells.items())))
        cells = step(cells)
    assert orbit[0] == orbit[2] == orbit[4] == orbit[6]
    assert orbit[1] == orbit[3] == orbit[5] == orbit[7]
    assert orbit[0] != orbit[1]
    return live_rows, orbit[:2]


if __name__ == "__main__":
    rows, phases = audit()
    print("live-output rows by target state:", rows)
    print("phase 0:", phases[0])
    print("phase 1:", phases[1])
