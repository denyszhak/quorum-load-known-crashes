"""Exact routes for interval quorums at n=q(q-2), q>=8, with two crashes.

Reads are all cyclic q-intervals; writes are their q-element hitting sets.
The claimed load q/(n-2) is a global upper bound, not a global optimum.
This generator uses rational arithmetic and no optimizer.
"""

import argparse
from bisect import bisect_right
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from math import lcm
from pathlib import Path


def circle_flow(inclusions, width):
    denominator = lcm(*(value.denominator for value in inclusions))
    weights = [int(value * denominator) for value in inclusions]
    assert sum(weights) == width * denominator
    assert all(0 <= value <= denominator for value in weights)
    cumulative = [0]
    for value in weights:
        cumulative.append(cumulative[-1] + value)
    cuts = sorted({0, denominator} | {value % denominator for value in cumulative})
    flow = {}
    for left, right in zip(cuts, cuts[1:]):
        points = [bisect_right(cumulative, left + j * denominator) - 1
                  for j in range(width)]
        assert len(set(points)) == width
        write = sum(1 << i for i in points)
        flow[write] = flow.get(write, 0) + right - left
    return {"mass": denominator, "weights": {str(mask): weight for mask, weight in flow.items()}}


def witness(q, failed):
    assert q >= 8
    n, m, count = q * (q - 2), q * (q - 2) - 2, q - 3
    failed = set(failed)
    assert len(failed) <= 2 and failed <= set(range(n))
    padded = set(failed)
    for i in range(n):
        if len(padded) == 2:
            break
        padded.add(i)
    x, y = sorted(padded)
    arcs = [list(range(x + 1, y)), list(range(y + 1, n)) + list(range(x))]
    arcs.sort(key=len)
    reads = {}

    def add(arc, start, probability):
        selected = arc[start:start + q]
        assert len(selected) == q
        mask = sum(1 << i for i in selected)
        reads[mask] = reads.get(mask, Fraction(0)) + probability

    exceptional = all(len(arc) % q == q - 1 for arc in arcs)
    if not exceptional:
        remaining = count
        for arc in arcs:
            blocks = min(remaining, len(arc) // q)
            offset = (len(arc) - blocks * q) // 2 if len(arcs[0]) == 0 else 0
            for j in range(blocks):
                add(arc, offset + j * q, Fraction(1, count))
            remaining -= blocks
        assert remaining == 0
    else:
        overlap = 0 if (len(arcs[0]) + 1) // q >= 2 else 1
        other = 1 - overlap
        arc, other_arc = arcs[overlap], arcs[other]
        blocks = (len(arc) + 1) // q
        low = Fraction(q, m)
        high = (1 - 2 * low) / (q - 5)
        for oriented in (arc, list(reversed(arc))):
            add(oriented, 0, low / 2)
            add(oriented, q - 1, low / 2)
            for j in range(2, blocks):
                add(oriented, j * q - 1, high / 2)
        other_blocks = (len(other_arc) + 1) // q - 1
        offset = (len(other_arc) - other_blocks * q) // 2
        for j in range(other_blocks):
            add(other_arc, offset + j * q, high)
    assert sum(reads.values()) == 1
    read_inclusion = [sum((prob for mask, prob in reads.items() if mask >> i & 1), Fraction(0))
                      for i in range(n)]
    pure = [Fraction(q, m) if i not in padded else Fraction(0) for i in range(n)]
    endpoint = [2 * pure[i] - read_inclusion[i] for i in range(n)]
    return {"q": q, "n": n, "failed": sorted(failed), "padded_failed": sorted(padded),
            "exceptional": exceptional,
            "reads": {str(mask): str(prob) for mask, prob in reads.items()},
            "uniform": circle_flow(pure, q), "balanced": circle_flow(endpoint, q)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--q", nargs="+", type=int, required=True)
    parser.add_argument("--all-pairs", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).read_bytes()
    (args.out / "source.py").write_bytes(source)
    cases = []
    for q in args.q:
        n = q * (q - 2)
        if args.all_pairs:
            placements = list(combinations(range(n), 2))
            coverage = "all labelled two-crash sets"
        else:
            placements = [(0, distance) for distance in range(1, n // 2 + 1)]
            coverage = "all two-crash classes up to rotation and reflection"
        placements += [(), (0,), (n - 1,)]
        rows = [witness(q, failed) for failed in placements]
        name = f"q{q}.json"
        (args.out / name).write_text(json.dumps({"q": q, "n": n, "coverage": coverage,
                                               "witnesses": rows}) + "\n")
        cases.append({"q": q, "n": n, "file": name, "witnesses": len(rows), "coverage": coverage})
        print(json.dumps(cases[-1]), flush=True)
    (args.out / "result.json").write_text(json.dumps({
        "source_sha256": hashlib.sha256(source).hexdigest(), "cases": cases,
        "scope": "Exact finite routing witnesses for a proposed infinite construction; global upper bounds only."
    }, indent=2) + "\n")
