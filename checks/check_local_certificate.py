"""Exhaustively check the two-label predecessor condition for a finite rule.

Coordinates use x east, y north. An offset names a predecessor relative to
the target; a parent-to-child step is its negation.

This module checks a finite local statement. It does not verify that a
spaceship exists or that a velocity bound is sharp.
"""

from itertools import product


def check_certificate(offsets, rule, steps_a, steps_b):
    """Return (valid, checked_live_rows, first_failure).

    `rule(bits)` receives one Boolean per offset in the given order.
    A failure records the bit row and its two witness-index sets.
    """
    offsets = tuple(offsets)
    steps_a = frozenset(steps_a)
    steps_b = frozenset(steps_b)
    if len(set(offsets)) != len(offsets):
        raise ValueError("Offsets must be distinct")
    available_steps = {(-x, -y) for x, y in offsets}
    if not (steps_a | steps_b) <= available_steps:
        raise ValueError("Permitted steps must be parent-to-child neighborhood steps")

    checked = 0
    for bits in product((False, True), repeat=len(offsets)):
        if not rule(bits):
            continue
        checked += 1
        a = tuple(i for i, ((x, y), live) in enumerate(zip(offsets, bits))
                  if live and (-x, -y) in steps_a)
        b = tuple(i for i, ((x, y), live) in enumerate(zip(offsets, bits))
                  if live and (-x, -y) in steps_b)
        if not a or not b or len(set(a) | set(b)) < 2:
            return False, checked, (bits, a, b)
    return True, checked, None


def toy_rule_demo():
    # W, NW, SW predecessor offsets, with north = positive y.
    offsets = ((-1, 0), (-1, 1), (-1, -1))
    def rule(bits):
        return bits[0] and (bits[1] or bits[2])

    # E and NE are A steps; E and SE are B steps.
    result = check_certificate(
        offsets, rule,
        steps_a=((1, 0), (1, 1)),
        steps_b=((1, 0), (1, -1)),
    )
    assert result == (True, 3, None), result
    return result


if __name__ == "__main__":
    print("Toy rule certificate:", toy_rule_demo())
