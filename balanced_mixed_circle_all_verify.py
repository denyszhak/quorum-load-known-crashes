"""Check exported all-placement circle routes using exact arithmetic only."""

import argparse
from copy import deepcopy
from fractions import Fraction
from itertools import combinations
import json
from math import lcm
from pathlib import Path
import shutil

from balanced_mixed_circle_short_arc_verify import bottleneck
from balanced_mixed_circle_verify import check, digest, relabel


def check_uniform(row: dict, n: int) -> None:
    phases = [{int(q): Fraction(p) for q, p in row[phase].items()} for phase in ("reads", "writes")]
    denominator = lcm(*(p.denominator for phase in phases for p in phase.values()))
    contacts = [0] * n
    for phase in phases:
        for quorum, probability in phase.items():
            mass = int(probability * denominator)
            while quorum:
                bit = quorum & -quorum
                contacts[bit.bit_length() - 1] += mass
                quorum ^= bit
    target = 2 * denominator * Fraction(row["load"])
    assert target.denominator == 1
    assert all(mass == (0 if row["failed"] >> i & 1 else target) for i, mass in enumerate(contacts))


def transform(row: dict, n: int, offset: int, sign: int, failed: int | None = None) -> dict:
    result = {**row, "failed": relabel(row["failed"], n, offset, sign) if failed is None else failed}
    for phase in ("reads", "writes"):
        result[phase] = {str(relabel(int(q), n, offset, sign)): p for q, p in row[phase].items()}
    return result


def audit(source: Path, out: Path) -> None:
    if out.exists():
        raise FileExistsError(out)
    root = Path(__file__).resolve().parent
    report = json.loads((source / "result.json").read_text())
    summaries = report["records"]
    if not summaries:
        raise ValueError("The manifest lists no balanced certificates.")
    listed_files = {f"r{summary['r']}.json" for summary in summaries}
    if len(listed_files) != len(summaries):
        raise ValueError("The manifest lists a balanced certificate rank more than once.")
    available_files = {path.name for path in source.glob("r[0-9]*.json")}
    if listed_files != available_files:
        raise ValueError("The manifest and the available balanced certificate files differ.")

    hashes = {str(source / "result.json"): digest(source / "result.json")}
    for name, expected in report["sources_sha256"].items():
        assert digest(root / name) == expected
        hashes[str(root / name)] = expected
    records, controls = [], []
    for summary in summaries:
        r, n = summary["r"], summary["n"]
        path = source / f"r{r}.json"
        doc = json.loads(path.read_text())
        assert r >= 5 and n == r * r - 1 and doc["r"] == r and doc["n"] == n
        lower = bottleneck(r)
        target = Fraction(lower["lower_bound"])
        assert target == Fraction(doc["load"]) == Fraction(summary["load"])
        routes = {row["failed"]: row for row in doc["witnesses"]}
        assert len(routes) == len(doc["witnesses"]) == summary["representatives"] == n // 2
        assert set(routes) == {1 | (1 << distance) for distance in range(1, n // 2 + 1)}
        intervals = {sum(1 << ((start + j) % n) for j in range(r)) for start in range(n)}
        tests, scenarios = 0, 0
        for row in routes.values():
            assert Fraction(row["load"]) == target
            tests += check(row, r, n, intervals)
            check_uniform(row, n)
            scenarios += 1
        if r <= 9:
            for count in range(3):
                for failed in combinations(range(n), count):
                    if count == 0:
                        base, offset, sign = 3, 0, 1
                    elif count == 1:
                        base, offset, sign = 3, failed[0], 1
                    else:
                        a, b = failed
                        distance = b - a
                        base = 1 | (1 << min(distance, n - distance))
                        offset, sign = a, 1 if distance <= n // 2 else -1
                    row = transform(routes[base], n, offset, sign, sum(1 << i for i in failed))
                    tests += check(row, r, n, intervals)
                    scenarios += 1
            coverage = "Every labelled failure set of size zero, one or two, plus representatives."
        else:
            for row in routes.values():
                for offset in (1, n // 2, n - 1):
                    for sign in (1, -1):
                        tests += check(transform(row, n, offset, sign), r, n, intervals)
                        scenarios += 1
            for failed in (0, 1, 1 << (n - 1)):
                offset = n - 1 if failed >> (n - 1) else 0
                tests += check(transform(routes[3], n, offset, 1, failed), r, n, intervals)
                scenarios += 1
            coverage = "Every distance representative, selected rotations and reflections, and padded zero/one-crash routes."
        for corruption in ("load", "normalization", "intersection", "mixture"):
            bad = deepcopy(doc["witnesses"][0])
            if corruption == "load":
                bad["load"] = "0"
            elif corruption == "normalization":
                quorum = next(iter(bad["reads"]))
                bad["reads"][quorum] = str(Fraction(bad["reads"][quorum]) + 1)
            elif corruption == "mixture":
                bad["smaller_write_probability"] = "1"
            else:
                quorum = next(iter(bad["writes"]))
                bad["writes"][str(sum(1 << i for i in range(2, r + 2)))] = bad["writes"].pop(quorum)
            try:
                check(bad, r, n, intervals)
            except AssertionError:
                controls.append({"r": r, "corruption": corruption})
            else:
                raise AssertionError("damaged certificate accepted")
        record = {**summary, "bottleneck": lower, "checked_routes": scenarios,
                  "global_intersection_tests": tests, "coverage": coverage,
                  "uniform_load_at_every_two_crash_survivor": True}
        records.append(record)
        hashes[str(path)] = digest(path)
        print(json.dumps(record), flush=True)
    out.mkdir(parents=True)
    snapshots = out / "source"
    snapshots.mkdir()
    for name in ("balanced_mixed_circle_all.py", "balanced_mixed_circle_all_verify.py",
                 "balanced_mixed_circle_short_arc.py", "balanced_mixed_circle_short_arc_verify.py",
                 "balanced_mixed_circle_verify.py", "balanced_circle.py"):
        hashes[str(root / name)] = digest(root / name)
        shutil.copy2(root / name, snapshots / name)
    result = {"valid": True, "date": "2026-10-12", "records": records,
              "rejected_corruptions": controls, "full_lean_formalization": False,
              "unrestricted_optimum_settled": False, "originality_established": False,
              "scope": "Exact checks of finite routes; arbitrary-r theorem has a separate written proof.",
              "sha256": hashes}
    (out / "manifest.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    audit(args.source.resolve(), args.out.resolve())
