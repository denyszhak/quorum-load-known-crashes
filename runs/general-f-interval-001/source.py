"""Direct routes for any f>=1 at n=(f+1)k, k>=f*f+1.

The written proof is in general_f_interval.md. This generator uses integer
systematic sampling, without a numerical solver. Replay is separate.
"""

import argparse
from bisect import bisect_right
import hashlib
from itertools import combinations
import json
from pathlib import Path
import random


def circle_flow(weights, width):
    assert sum(weights) % width == 0
    mass = sum(weights) // width
    assert mass > 0 and all(0 <= value <= mass for value in weights)
    cumulative = [0]
    for value in weights:
        cumulative.append(cumulative[-1] + value)
    cuts = sorted({0, mass} | {value % mass for value in cumulative})
    flow = {}
    for left, right in zip(cuts, cuts[1:]):
        points = [bisect_right(cumulative, left + j * mass) - 1
                  for j in range(width)]
        assert len(set(points)) == width
        write = sum(1 << i for i in points)
        flow[write] = flow.get(write, 0) + right - left
    assert sum(flow.values()) == mass
    return flow


def witness(faults, k, failed):
    assert faults >= 1 and k >= faults * faults + 1
    n, rank, width = (faults + 1) * k, k + faults, faults + 1
    failed = set(failed)
    assert len(failed) <= faults and failed <= set(range(n))
    padded = set(failed)
    for i in range(n):
        if len(padded) == faults:
            break
        padded.add(i)
    ordered = sorted(padded)
    arcs = [((ordered[(j + 1) % faults] - start - 1) % n, start)
            for j, start in enumerate(ordered)]
    length, start = max(arcs)
    assert length >= rank
    read = {(start + j + 1) % n for j in range(rank)}
    assert read.isdisjoint(padded)
    pure = [width if i not in padded else 0 for i in range(n)]
    endpoint = [rank - int(i in read) if i not in padded else 0
                for i in range(n)]
    return {"f": faults, "k": k, "n": n, "failed": sorted(failed),
            "padded_failed": sorted(padded), "read": sorted(read),
            "uniform": {str(q): value for q, value in circle_flow(pure, width).items()},
            "endpoint": {str(q): value for q, value in circle_flow(endpoint, width).items()}}


def placements(n, faults):
    if faults <= 3:
        representatives = []
        for rest in combinations(range(1, n), faults - 1):
            failed = (0, *rest)
            gaps = tuple((failed[(j + 1) % faults] - failed[j] - 1) % n
                         for j in range(faults))
            if gaps == min(gaps[j:] + gaps[:j] for j in range(faults)):
                representatives.append(failed)
        return representatives, "all cyclic exact-f failure classes"
    selected = {tuple(range(faults)), tuple(range(n - faults, n)),
                tuple(j * n // faults for j in range(faults))}
    for split in range(1, faults):
        selected.add(tuple(sorted((*range(split),
                                  *range(n // 2, n // 2 + faults - split)))))
    rng = random.Random(8675309 + n + faults)
    for _ in range(32):
        selected.add(tuple(sorted(rng.sample(range(n), faults))))
    return sorted(selected), "selected exact-f failure sets"


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--cases", nargs="+", required=True, help="f:k pairs")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    source = Path(__file__).read_bytes()
    (args.out / "source.py").write_bytes(source)
    records = []
    for case in args.cases:
        faults, k = map(int, case.split(":"))
        assert faults >= 1 and k >= faults * faults + 1
        n = (faults + 1) * k
        failed_sets, coverage = placements(n, faults)
        failed_sets += [tuple(range(j)) for j in range(faults)]
        rows = [witness(faults, k, failed) for failed in failed_sets]
        name = f"f{faults}-k{k}.json"
        (args.out / name).write_text(json.dumps({"f": faults, "k": k, "n": n,
                                               "coverage": coverage, "witnesses": rows}) + "\n")
        records.append({"f": faults, "k": k, "n": n, "file": name,
                        "witnesses": len(rows), "coverage": coverage})
        print(json.dumps(records[-1]), flush=True)
    (args.out / "result.json").write_text(json.dumps({
        "source_sha256": hashlib.sha256(source).hexdigest(), "cases": records,
        "scope": "Finite implementation controls for the written arbitrary-f theorem; no Lean or originality claim."
    }, indent=2) + "\n")
