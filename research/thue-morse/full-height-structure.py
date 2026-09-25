"""Bounded run-pattern discovery for the full-height conjecture; not a proof."""
import json


def bit(n):
    return n.bit_count() & 1


def runs(values):
    out = []
    for x in values:
        if out and out[-1][0] == x:
            out[-1][1] += 1
        else:
            out.append([x, 1])
    return out


def trace(h, q, parity):
    z = (4*h+2)*q
    start = z - 2 + parity
    a, b = start, start+1
    da, db = [], []
    for k in range(16*q+1):
        if a == b:
            return {"h": h, "q": q, "parity": parity, "height": k-1,
                    "last_offset": a-z, "left": runs(da), "right": runs(db)}
        aa = 1 if bit(a+1) == bit(k) else 2
        bb = 1 if bit(b+1) == bit(k) else 2
        da.append(aa)
        db.append(bb)
        a += aa
        b += bb
    raise AssertionError((h,q,parity))


if __name__ == "__main__":
    result = [trace(h,q,parity) for h,parity in [(0,0),(3,0),(5,0),(9,0),
              (2,1),(4,1),(7,1),(13,1),(1,1),(25,1)] for q in [4,8,16]]
    print(json.dumps(result, indent=2))
