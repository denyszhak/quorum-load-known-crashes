"""One centered-read rule for all nonexceptional two-crash cluster sizes."""

import argparse
from bisect import bisect_right
import hashlib
from itertools import combinations
import json
from pathlib import Path


def circle_flow(weights):
    assert sum(weights) % 3 == 0
    mass = sum(weights) // 3
    assert mass > 0 and all(0 <= value <= mass for value in weights)
    cumulative = [0]
    for value in weights:
        cumulative.append(cumulative[-1] + value)
    cuts = sorted({0, mass} | {value % mass for value in cumulative})
    result = {}
    for left, right in zip(cuts, cuts[1:]):
        points = [bisect_right(cumulative, left + j * mass) - 1 for j in range(3)]
        assert len(set(points)) == 3
        write = sum(1 << i for i in points)
        result[write] = result.get(write, 0) + right - left
    assert sum(result.values()) == mass
    return result


def witness(n, failed):
    k, residue = divmod(n, 3)
    assert k >= 3 and n not in {9, 10, 11, 12, 14, 17, 20}
    rank = k + 2
    numerator = residue + 1
    failed = set(failed)
    assert failed <= set(range(n)) and len(failed) <= 2
    padded = set(failed)
    for i in range(n):
        if len(padded) == 2:
            break
        padded.add(i)
    first, second = sorted(padded)
    distance = second - first
    if distance > n // 2:
        first, distance = second, n - distance
    short, long = distance - 1, n - distance - 1
    if short >= rank:
        starts = [first + 1, first + distance + 1]
        case = "one interval in each live arc"
    else:
        slack = long - rank
        assert slack >= 0
        starts = [first + distance + 1 + slack // 2,
                  first + distance + 1 + (slack + 1) // 2]
        case = "two centered intervals in the longer live arc"
    reads = [{(start + j) % n for j in range(rank)} for start in starts]
    assert all(read.isdisjoint(padded) for read in reads)
    pure = [3 if i not in padded else 0 for i in range(n)]
    endpoint = [2 * rank - numerator * sum(i in read for read in reads) if i not in padded else 0
                for i in range(n)]
    return {"n": n, "failed": sorted(failed), "padded_failed": sorted(padded),
            "reads": [sorted(read) for read in reads], "case": case,
            "uniform": {str(q): value for q, value in circle_flow(pure).items()},
            "endpoint": {str(q): value for q, value in circle_flow(endpoint).items()}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, nargs="+", required=True)
    parser.add_argument("--all-failures-through", type=int, default=35)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).read_bytes()
    (args.out / "source.py").write_bytes(source)
    cases = []
    for n in args.nodes:
        failures = (list(combinations(range(n), 2)) if n <= args.all_failures_through else
                    [(0, d) for d in range(1, n // 2 + 1)])
        failures += [(), (0,), (n // 2,)]
        rows = [witness(n, failed) for failed in failures]
        coverage = "all exact-two sets" if n <= args.all_failures_through else "all distances up to reflection"
        name = f"n{n}.json"
        (args.out / name).write_text(json.dumps({"n": n, "coverage": coverage, "witnesses": rows}) + "\n")
        cases.append({"n": n, "file": name, "coverage": coverage, "witnesses": len(rows)})
        print(json.dumps(cases[-1]), flush=True)
    (args.out / "result.json").write_text(json.dumps({"source_sha256": hashlib.sha256(source).hexdigest(),
        "cases": cases, "scope": "Finite controls; the separate proof supplies the arbitrary-size theorem."}, indent=2) + "\n")
