"""Check actual mixed-size circle routes without optimization code."""

import argparse
from copy import deepcopy
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from math import lcm
from pathlib import Path
import shutil


if not __debug__:
    raise RuntimeError(
        "Verification requires assertions. Run without -O and unset PYTHONOPTIMIZE."
    )


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def relabel(mask: int, n: int, offset: int, sign: int) -> int:
    result = 0
    while mask:
        bit = mask & -mask
        result |= 1 << ((offset + sign * (bit.bit_length() - 1)) % n)
        mask ^= bit
    return result


def check(row: dict, r: int, n: int, intervals: set[int]) -> int:
    failed = row["failed"]
    assert 0 <= failed < 1 << n and failed.bit_count() <= 2
    assert row["read_fraction"] == "1/2"
    phases = [{int(q): Fraction(p) for q, p in row[phase].items()} for phase in ("reads", "writes")]
    assert all(p and sum(p.values()) == 1 and min(p.values()) > 0 for p in phases)
    denominator = lcm(*(p.denominator for phase in phases for p in phase.values()))
    contacts = [0] * n
    tests = 0
    for index, phase in enumerate(phases):
        for q, probability in phase.items():
            assert 0 < q < 1 << n and not q & failed
            if index == 0:
                assert q in intervals
            else:
                assert q.bit_count() in (r, r + 1)
                assert all(q & read for read in intervals)
                tests += len(intervals)
            weight = int(probability * denominator)
            assert Fraction(weight, denominator) == probability
            mask = q
            while mask:
                bit = mask & -mask
                contacts[bit.bit_length() - 1] += weight
                mask ^= bit
    assert all(contacts[i] == 0 for i in range(n) if failed & (1 << i))
    assert Fraction(max(contacts), 2 * denominator) == Fraction(row["load"])
    small = sum((p for q, p in phases[1].items() if q.bit_count() == r), Fraction(0))
    assert small == Fraction(row["smaller_write_probability"])
    return tests


def audit(source: Path, out: Path) -> None:
    assert __debug__ and not out.exists()
    out.mkdir(parents=True)
    root = Path(__file__).resolve().parent
    report = json.loads((source / "result.json").read_text())
    hashes = {str(source / "result.json"): digest(source / "result.json")}
    for name, expected in report["sources_sha256"].items():
        assert digest(root / name) == expected
        hashes[str(root / name)] = expected
    records, controls = [], []
    for summary in report["records"]:
        r, n = summary["r"], summary["n"]
        assert n == r * r - 1
        path = source / f"r{r}.json"
        doc = json.loads(path.read_text())
        assert doc["r"] == r and doc["n"] == n and doc["load"] == summary["load"]
        intervals = {sum(1 << ((s + j) % n) for j in range(r)) for s in range(n)}
        routes = {row["failed"]: row for row in doc["witnesses"]}
        assert len(routes) == len(doc["witnesses"]) == summary["representatives"]
        assert set(routes) == {1 | (1 << d) for d in range(1, n // 2 + 1)}
        for row in routes.values():
            check(row, r, n, intervals)
        tests, scenarios = 0, 0
        for count in range(3):
            for failed in combinations(range(n), count):
                if count == 0:
                    base, offset, sign = 3, 0, 1
                elif count == 1:
                    base, offset, sign = 3, failed[0], 1
                else:
                    a, b = failed
                    d = b - a
                    base, offset, sign = 1 | (1 << min(d, n - d)), a, 1 if d <= n // 2 else -1
                row = {**routes[base], "failed": sum(1 << i for i in failed)}
                for phase in ("reads", "writes"):
                    row[phase] = {str(relabel(int(q), n, offset, sign)): p
                                  for q, p in routes[base][phase].items()}
                tests += check(row, r, n, intervals)
                scenarios += 1
        assert scenarios == 1 + n + n * (n - 1) // 2
        upper = max(Fraction(row["load"]) for row in routes.values())
        assert upper == Fraction(doc["load"]) < Fraction(1, r - 1)
        for name in ("load", "normalization", "illegal_write"):
            bad = deepcopy(doc["witnesses"][0])
            if name == "load":
                bad["load"] = "0"
            elif name == "normalization":
                q = next(iter(bad["reads"]))
                bad["reads"][q] = str(Fraction(bad["reads"][q]) + 1)
            else:
                q = next(iter(bad["writes"]))
                bad["writes"]["1"] = bad["writes"].pop(q)
            try:
                check(bad, r, n, intervals)
            except AssertionError:
                controls.append({"r": r, "corruption": name})
            else:
                raise AssertionError("damaged route accepted")
        record = {"r": r, "n": n, "upper_bound": str(upper),
                  "labelled_scenarios": scenarios, "global_intersection_tests": tests}
        records.append(record)
        hashes[str(path)] = digest(path)
        print(json.dumps(record), flush=True)
    snapshots = out / "source"
    snapshots.mkdir()
    for name in ("balanced_mixed_circle_certify.py", "balanced_mixed_circle_verify.py",
                 "balanced_mixed_circle.py", "balanced_near_square.py", "balanced_circle.py"):
        path = root / name
        hashes[str(path)] = digest(path)
        shutil.copy2(path, snapshots / name)
    for name in ("balanced_mixed_circle.md", "paper/quorum-two-crashes.tex", "paper/originality-review-brief.tex"):
        path = root / name
        hashes[str(path)] = digest(path)
    result = {"valid": True, "date": "2026-10-12", "records": records,
              "rejected_corruptions": controls, "general_formula_proved": False,
              "global_optimality_proved": False, "originality_established": False,
              "scope": "Finite actual routing upper bounds, checked after every labelled failed set of size at most two.",
              "sha256": hashes}
    (out / "manifest.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    audit(args.source.resolve(), args.out.resolve())
