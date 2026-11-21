"""Independent exact checks for finite searches and direct interval routes.

Imports neither route generator nor numerical solvers. The unbounded
conclusion comes from the accompanying proof, not finite enumeration.
"""

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from pathlib import Path

from verify import verify


def check_finite(path):
    result = json.loads(path.read_text())
    n, rank = result["n"], result["n"] // 3 + 2
    critical = Fraction(n % 3 + 1, (n // 3) ** 2 + n // 3 + n % 3 - 1)
    assert Fraction(result["critical_alpha"]) == critical
    certificate = result["certificate"]
    assert certificate is not None and not result.get("representatives_only", False)
    case, candidate = certificate["instance"], certificate["candidate"]
    assert case["n"] == n
    assert case["read_capacity"] == case["write_capacity"] == ["1"] * n
    assert all(q.bit_count() == rank for q in candidate["reads"])
    assert all(q.bit_count() == 3 for q in candidate["writes"])
    expected = {(sum(1 << i for i in f), a) for count in range(3)
                for f in combinations(range(n), count)
                for a in (Fraction(0), critical / 2, critical)}
    actual = [(row["failed"], Fraction(row["read_fraction"])) for row in case["scenarios"]]
    assert len(actual) == len(expected) and set(actual) == expected
    checked = verify(case, candidate)
    for a in (Fraction(0), critical / 2, critical):
        worst = max(Fraction(row["load"]) for row in candidate["scenarios"]
                    if Fraction(row["read_fraction"]) == a)
        assert worst == (3 + (n // 3 - 1) * a) / (n - 2)
    return {"n": n, "valid": True, "scenarios": checked["scenarios"],
            "critical_alpha": str(critical),
            "endpoint_load": str((3 + (n // 3 - 1) * critical) / (n - 2))}


def check_direct(row):
    n = row["n"]
    k, residue = divmod(n, 3)
    rank, numerator = k + 2, residue + 1
    assert (residue == 0 and k >= 5) or (residue == 1 and k >= 4)
    failed, padded, read = map(set, (row["failed"], row["padded_failed"], row["read"]))
    assert failed <= padded <= set(range(n)) and len(padded) == 2
    intervals = [{(start + j) % n for j in range(rank)} for start in range(n)]
    assert read in intervals and len(read) == rank and read.isdisjoint(padded)
    critical = Fraction(numerator, k * k + k + residue - 1)
    assert Fraction(row["critical_alpha"]) == critical
    masses = {"uniform": Fraction(n - 2, 3), "endpoint": Fraction((k - 1) * rank)}
    for kind in ("uniform", "endpoint"):
        flow = {int(q): Fraction(value) for q, value in row[kind].items()}
        assert flow and all(value > 0 for value in flow.values())
        degrees = [Fraction(0)] * n
        for q, value in flow.items():
            assert 0 < q < 1 << n
            members = {i for i in range(n) if q & (1 << i)}
            assert len(members) == 3 and members.isdisjoint(padded)
            assert all(not members.isdisjoint(interval) for interval in intervals)
            for i in members:
                degrees[i] += value
        expected = [Fraction(0) if i in padded else
                    Fraction(1 if kind == "uniform" else rank - numerator * int(i in read))
                    for i in range(n)]
        assert degrees == expected
        assert sum(flow.values()) == masses[kind]
        assert max(expected) <= masses[kind]
        assert all(sum(expected[i] for i in interval) >= masses[kind] for interval in intervals)
    for a in (Fraction(0), critical / 4, critical / 2, 3 * critical / 4, critical):
        lam = a / critical
        target = (3 + (k - 1) * a) / (n - 2)
        for i in range(n):
            if i in padded:
                load = Fraction(0)
            else:
                load = (a * int(i in read) + (1 - lam) * Fraction(3, n - 2)
                        + lam * (1 - critical) * Fraction(rank - numerator * int(i in read), (k - 1) * rank))
            assert load == (Fraction(0) if i in padded else target)
        assert (1 - lam) + lam * (1 - critical) == 1 - a


def check_bounds():
    checks = 0
    for k in range(3, 201):
        for residue in range(3):
            n, denominator = 3 * k + residue, k * k + k + residue - 1
            critical = Fraction(residue + 1, denominator)
            for a in (Fraction(0), critical / 2, critical, Fraction(1)):
                average = (3 + (k - 1) * a) / (n - 2)
                difference = (1 - a) / (k - 1) - average
                assert difference == Fraction(residue + 1 - denominator * a, (k - 1) * (n - 2))
                checks += 1
            assert (3 + (k - 1) * critical) / (n - 2) == Fraction(k + 2, denominator)
            if residue < 2:
                small = set(range(0, n, 3))
                writes = [{(s + e * j) % n for j in range(3)}
                          for s in range(n) for e in (1, 2)]
                assert all(small & write for write in writes)
                assert Fraction(1, len(small) - 2) > Fraction(3, n - 2)
    return checks


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--finite", type=Path, required=True)
    parser.add_argument("--direct", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    finite = [check_finite(path) for path in sorted(args.finite.glob("n*/result.json"))]
    assert {row["n"] for row in finite} >= {9, 10, 12, 13, 15, 16}
    direct = []
    for path in sorted(args.direct.glob("n*.json")):
        result = json.loads(path.read_text())
        n, rows = result["n"], result["witnesses"]
        if result["coverage"] == "all exact-two sets":
            assert {tuple(row["failed"]) for row in rows if len(row["failed"]) == 2} == set(combinations(range(n), 2))
        else:
            assert {(0, d) for d in range(1, n // 2 + 1)} <= {tuple(row["failed"]) for row in rows}
        for row in rows:
            check_direct(row)
        direct.append({"n": n, "valid": True, "witnesses": len(rows), "coverage": result["coverage"]})
        print(json.dumps(direct[-1]), flush=True)
    control = json.loads(next(args.direct.glob("n*.json")).read_text())["witnesses"][0]
    damaged = deepcopy(control)
    first = next(iter(damaged["uniform"]))
    damaged["uniform"][first] = str(Fraction(damaged["uniform"][first]) + Fraction(1, 3))
    try:
        check_direct(damaged)
    except AssertionError:
        pass
    else:
        raise AssertionError("Corrupted flow was accepted")
    root = Path(__file__).resolve().parent
    inputs = list(args.finite.glob("n*/result.json")) + list(args.direct.glob("*.json"))
    inputs += [args.finite / "source.py", args.direct / "source.py"]
    record = {"valid": True, "finite": finite, "direct": direct,
              "bound_arithmetic_controls": check_bounds(),
              "finite_scenarios": sum(row["scenarios"] for row in finite),
              "direct_witnesses": sum(row["witnesses"] for row in direct),
              "checker_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "input_sha256": {str(path.resolve().relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs},
              "corrupted_flow_rejected": True,
              "scope": "Independent rational replay; arbitrary-size claims rely on the written proof and are not yet Lean theorems."}
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / "result.json").write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({key: value for key, value in record.items() if key not in ("finite", "direct")}), flush=True)
