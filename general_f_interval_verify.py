"""Independent integer/rational replay; imports no generator or solver."""

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


def members(mask):
    result = []
    while mask:
        bit = mask & -mask
        result.append(bit.bit_length() - 1)
        mask -= bit
    return result


def canonical(failed, n):
    return min(tuple(sorted((i - origin) % n for i in failed)) for origin in failed)


def check(row):
    faults, k, n = row["f"], row["k"], row["n"]
    assert faults >= 1 and k >= faults * faults + 1 and n == (faults + 1) * k
    rank, width, live = k + faults, faults + 1, n - faults
    mass = (k - 1) * rank
    failed, padded, read = map(set, (row["failed"], row["padded_failed"], row["read"]))
    assert len(failed) <= faults and failed <= padded <= set(range(n))
    assert len(padded) == faults and len(read) == rank and read.isdisjoint(padded)
    intervals = [sum(1 << ((start + j) % n) for j in range(rank)) for start in range(n)]
    assert sum(1 << i for i in read) in intervals
    padded_mask = sum(1 << i for i in padded)
    for kind, total in (("uniform", live), ("endpoint", mass)):
        flow = {int(q): value for q, value in row[kind].items()}
        assert flow and all(type(value) is int and value > 0 for value in flow.values())
        assert sum(flow.values()) == total
        degrees = [0] * n
        for write, value in flow.items():
            assert 0 < write < 1 << n and write.bit_count() == width
            assert not write & padded_mask
            assert all(write & interval for interval in intervals)
            for i in members(write):
                degrees[i] += value
        expected = [0 if i in padded else
                    width if kind == "uniform" else rank - int(i in read) for i in range(n)]
        assert degrees == expected
        assert all(sum(expected[i] for i in members(interval)) >= total for interval in intervals)
        assert max(expected) <= total
    critical = Fraction(1, mass + 1)
    for alpha in (Fraction(0), critical / 2, critical):
        lam = alpha / critical
        assert (1 - lam) + lam * (1 - critical) == 1 - alpha
        target = (width + (k - 1) * alpha) / live
        for i in range(n):
            load = (Fraction(0) if i in padded else
                    alpha * int(i in read) + (1 - lam) * Fraction(width, live)
                    + lam * (1 - critical) * Fraction(rank - int(i in read), mass))
            assert load == (0 if i in padded else target)


def arithmetic():
    count = 0
    for faults in range(1, 21):
        for extra in (0, 1, 2, 17):
            k = faults * faults + 1 + extra
            n, rank = (faults + 1) * k, k + faults
            live, mass = n - faults, (k - 1) * rank
            critical = Fraction(1, mass + 1)
            assert live > faults * (rank - 1)
            assert k * (rank - 1) == mass + faults
            for alpha in (Fraction(0), critical / 2, critical, Fraction(1)):
                average = (faults + 1 + (k - 1) * alpha) / live
                assert (1 - alpha) / (k - 1) - average == Fraction(
                    1 - (mass + 1) * alpha, (k - 1) * live)
                count += 1
    return count


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    source = json.loads((args.source / "result.json").read_text())
    assert hashlib.sha256((args.source / "source.py").read_bytes()).hexdigest() == source["source_sha256"]
    records = []
    inputs = [args.source / "result.json", args.source / "source.py"]
    for case in source["cases"]:
        path = args.source / case["file"]
        inputs.append(path)
        record = json.loads(path.read_text())
        faults, n, rows = record["f"], record["n"], record["witnesses"]
        assert faults == case["f"] and record["k"] == case["k"] and n == case["n"]
        assert record["coverage"] == case["coverage"] and len(rows) == case["witnesses"]
        assert all(row["f"] == faults and row["k"] == case["k"] and row["n"] == n for row in rows)
        if record["coverage"] == "all cyclic exact-f failure classes":
            assert faults <= 3
            expected = {canonical((0, *rest), n) for rest in combinations(range(1, n), faults - 1)}
            actual = [canonical(row["failed"], n) for row in rows if len(row["failed"]) == faults]
            assert len(actual) == len(expected) and set(actual) == expected
        else:
            assert record["coverage"] == "selected exact-f failure sets"
        for row in rows:
            check(row)
        assert {len(row["failed"]) for row in rows} == set(range(faults + 1))
        records.append({**case, "valid": True})
        print(json.dumps(records[-1]), flush=True)
    damaged = deepcopy(rows[0])
    first = next(iter(damaged["endpoint"]))
    damaged["endpoint"][first] += 1
    try:
        check(damaged)
    except AssertionError:
        pass
    else:
        raise AssertionError("Damaged endpoint flow was accepted")
    root = Path(__file__).resolve().parent
    result = {"valid": True, "cases": records, "witnesses": sum(row["witnesses"] for row in records),
              "arithmetic_controls": arithmetic(), "corrupted_flow_rejected": True,
              "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "input_sha256": {str(path.resolve().relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
                               for path in inputs},
              "scope": "Independent exact finite replay. Unbounded validity is supplied by the written proof, not Lean or finite extrapolation."}
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key not in ("cases", "input_sha256")}), flush=True)
