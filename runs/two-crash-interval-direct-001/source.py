"""Direct rational routes for n=3k (k>=5) and n=3k+1 (k>=4).

Reads are cyclic intervals of length floor(n/3)+2; writes hit every
such interval. Weighted systematic sampling supplies the write flows.
The accompanying written argument, not a finite test count, covers all n.
"""

import argparse
from bisect import bisect_right
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from pathlib import Path


def choose_read(n, failed):
    k, residue = divmod(n, 3)
    rank = k + 2
    assert (residue == 0 and k >= 5) or (residue == 1 and k >= 4)
    first, second = sorted(failed)
    distance = second - first
    if distance > n // 2:
        first, distance = second, n - distance
    if residue == 1 and distance < rank:
        start = rank - max(0, 4 - distance)
        read = {(first + start + j) % n for j in range(rank)}
    else:
        read = next({(start + j) % n for j in range(rank)}
                    for start in range(n)
                    if all((start + j) % n not in failed for j in range(rank)))
    assert read.isdisjoint(failed)
    return read


def circle_flow(weights):
    weights = list(map(Fraction, weights))
    mass = sum(weights) / 3
    assert mass > 0 and all(0 <= value <= mass for value in weights)
    cumulative = [Fraction(0)]
    for value in weights:
        cumulative.append(cumulative[-1] + value)
    cuts = sorted({Fraction(0), mass} | {value % mass for value in cumulative})
    flow = {}
    for left, right in zip(cuts, cuts[1:]):
        offset = (left + right) / 2
        points = [bisect_right(cumulative, offset + j * mass) - 1 for j in range(3)]
        assert len(set(points)) == 3
        write = sum(1 << i for i in points)
        flow[write] = flow.get(write, Fraction(0)) + right - left
    assert sum(flow.values()) == mass
    return flow


def witness(n, failed):
    failed = set(failed)
    assert len(failed) <= 2 and failed <= set(range(n))
    padded = set(failed)
    for i in range(n):
        if len(padded) == 2:
            break
        padded.add(i)
    k, residue = divmod(n, 3)
    rank, numerator = k + 2, residue + 1
    read = choose_read(n, padded)
    uniform_weights = [int(i not in padded) for i in range(n)]
    endpoint_weights = [(rank - numerator * int(i in read)) if i not in padded else 0
                        for i in range(n)]
    uniform, endpoint = circle_flow(uniform_weights), circle_flow(endpoint_weights)
    return {"n": n, "failed": sorted(failed), "padded_failed": sorted(padded),
            "read": sorted(read),
            "uniform": {str(q): str(v) for q, v in uniform.items()},
            "endpoint": {str(q): str(v) for q, v in endpoint.items()},
            "critical_alpha": str(Fraction(numerator, k * k + k + residue - 1))}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, nargs="+", required=True)
    parser.add_argument("--all-failures-through", type=int, default=40)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).read_bytes()
    (args.out / "source.py").write_bytes(source)
    records = []
    for n in args.nodes:
        failures = (list(combinations(range(n), 2)) if n <= args.all_failures_through else
                    [(0, d) for d in range(1, n // 2 + 1)])
        failures += [(), (0,), (n // 2,)]
        rows = [witness(n, failed) for failed in failures]
        record = {"n": n, "witnesses": rows,
                  "coverage": "all exact-two sets" if n <= args.all_failures_through else
                  "all relative distances, plus padding controls"}
        (args.out / f"n{n}.json").write_text(json.dumps(record) + "\n")
        records.append({"n": n, "witnesses": len(rows), "coverage": record["coverage"]})
        print(json.dumps(records[-1]), flush=True)
    (args.out / "result.json").write_text(json.dumps({
        "source_sha256": hashlib.sha256(source).hexdigest(), "cases": records,
        "scope": "Exact finite controls for the separate arbitrary-size written proof; no Lean claim."
    }, indent=2) + "\n")
