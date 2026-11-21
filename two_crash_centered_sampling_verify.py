"""Independent exact replay of the unified centered-read construction."""

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from pathlib import Path


if not __debug__:
    raise RuntimeError(
        "Verification requires assertions. Run without -O and unset PYTHONOPTIMIZE."
    )


def bitset(indices):
    return sum(1 << i for i in indices)


def check(row):
    n = row["n"]
    k, residue = divmod(n, 3)
    assert k >= 3 and n not in {9, 10, 11, 12, 14, 17, 20}
    rank, mass = k + 2, (k - 1) * (k + 2)
    numerator = residue + 1
    failed, padded = set(row["failed"]), set(row["padded_failed"])
    assert failed <= padded <= set(range(n)) and len(failed) <= 2 and len(padded) == 2
    reads = list(map(set, row["reads"]))
    windows = [bitset((start + j) % n for j in range(rank)) for start in range(n)]
    assert len(reads) == 2
    for read in reads:
        assert len(read) == rank and read.isdisjoint(padded) and bitset(read) in windows
    counts = [sum(i in read for read in reads) for i in range(n)]
    weights = {
        "uniform": [3 if i not in padded else 0 for i in range(n)],
        "endpoint": [2 * rank - numerator * counts[i] if i not in padded else 0 for i in range(n)],
    }
    masses = {"uniform": n - 2, "endpoint": 2 * mass}
    degrees = {}
    for name, values in weights.items():
        flow = {int(q): value for q, value in row[name].items()}
        h = masses[name]
        assert sum(values) == 3 * h and all(0 <= value <= h for value in values)
        assert sum(flow.values()) == h
        for window in windows:
            assert sum(values[i] for i in range(n) if window >> i & 1) >= h
        degree = [0] * n
        for write, coefficient in flow.items():
            assert 0 < coefficient and isinstance(coefficient, int)
            assert 0 <= write < 1 << n and write.bit_count() == 3
            assert not write & bitset(padded)
            assert all(write & window for window in windows)
            for i in range(n):
                if write >> i & 1:
                    degree[i] += coefficient
        assert degree == values
        degrees[name] = degree
    a0 = Fraction(numerator, mass + numerator)
    for a in (Fraction(0), a0 / 2, a0):
        lam = a / a0
        target = Fraction(3 + (k - 1) * a, n - 2)
        for i in range(n):
            load = (a * Fraction(counts[i], 2)
                    + (1 - lam) * Fraction(degrees["uniform"][i], masses["uniform"])
                    + lam * (1 - a0) * Fraction(degrees["endpoint"][i], masses["endpoint"]))
            assert load == (Fraction(0) if i in padded else target)


def obstruction():
    records = []
    for k in range(3, 7):
        rank, n = k + 2, 3 * k + 2
        failed = {0, rank}
        reads = [{(s + j) % n for j in range(rank)} for s in range(n)]
        live = [r for r in reads if r.isdisjoint(failed)]
        left = set(range(rank, 2 * rank))
        right = set(range(n - rank + 1, n)) | {0}
        assert live and left in reads and right in reads
        assert len(left & failed) == len(right & failed) == 1
        assert all(len(r & left) + len(r & right) == rank + 3 for r in live)
        alpha = Fraction(3, (k - 1) * rank + 3)
        bound = (2 + (rank + 1) * alpha) / (2 * (rank - 1))
        optimum = Fraction(rank, (k - 1) * rank + 3)
        assert bound > optimum
        assert bound - optimum == Fraction(9 - rank, 2 * (rank - 1) * ((k - 1) * rank + 3))
        records.append({"n": n, "failed": sorted(failed), "live_reads": len(live),
                        "interval_load_lower_bound_at_endpoint": str(bound),
                        "unrestricted_optimum_at_endpoint": str(optimum)})
    return records


def unavailable_reads():
    records = []
    for n, failed in ((9, {0, 4}), (10, {0, 5}), (12, {0, 6})):
        rank = n // 3 + 2
        reads = [{(start + j) % n for j in range(rank)} for start in range(n)]
        assert not any(read.isdisjoint(failed) for read in reads)
        records.append({"n": n, "failed": sorted(failed), "live_reads": 0})
    return records


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    manifest = json.loads((args.source / "result.json").read_text())
    assert hashlib.sha256((args.source / "source.py").read_bytes()).hexdigest() == manifest["source_sha256"]
    inputs = [args.source / "result.json", args.source / "source.py"]
    cases = []
    for case in manifest["cases"]:
        path = args.source / case["file"]
        inputs.append(path)
        record = json.loads(path.read_text())
        n, rows = record["n"], record["witnesses"]
        assert n == case["n"] and len(rows) == case["witnesses"] and record["coverage"] == case["coverage"]
        exact = [tuple(row["failed"]) for row in rows if len(row["failed"]) == 2]
        if case["coverage"] == "all exact-two sets":
            assert set(exact) == set(combinations(range(n), 2)) and len(exact) == n * (n - 1) // 2
        else:
            assert case["coverage"] == "all distances up to reflection"
            assert set(exact) == {(0, d) for d in range(1, n // 2 + 1)} and len(exact) == n // 2
        assert {len(row["failed"]) for row in rows} == {0, 1, 2}
        assert all(row["n"] == n for row in rows)
        for row in rows:
            check(row)
        cases.append({**case, "valid": True})
        print(json.dumps(cases[-1]), flush=True)
    damaged = deepcopy(rows[0])
    first = next(iter(damaged["endpoint"]))
    damaged["endpoint"][first] += 1
    try:
        check(damaged)
    except AssertionError:
        pass
    else:
        raise AssertionError("Corrupted flow accepted")
    root = Path(__file__).resolve().parent
    result = {"valid": True, "cases": cases, "witnesses": sum(c["witnesses"] for c in cases),
              "small_size_obstructions": obstruction(), "unavailable_read_controls": unavailable_reads(),
              "corrupted_flow_rejected": True,
              "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "input_sha256": {str(p.resolve().relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs},
              "scope": "Independent finite replay for the unified two-crash interval construction and all seven exceptional sizes. The general selection proof is written, not fully formalized in Lean."}
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key not in ("cases", "input_sha256")}), flush=True)
