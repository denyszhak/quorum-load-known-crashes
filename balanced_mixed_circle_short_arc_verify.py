"""Independently check the explicit routes and the bottleneck geometry."""

import argparse
from copy import deepcopy
from fractions import Fraction
import json
from pathlib import Path
import shutil

from balanced_mixed_circle_verify import check, digest, relabel


def bottleneck(r: int) -> dict:
    n = r * r - 1
    failed = 1 | (1 << r)
    side = sum(1 << i for i in range(r + 1, n))
    intervals = {sum(1 << ((start + j) % n) for j in range(r)) for start in range(n)}
    parts = [sum(1 << ((block * r + j) % n) for j in range(r)) & ~failed
             for block in range(1, r)]
    union = 0
    for part in parts:
        assert part and part & ~side == 0 and not part & union
        union |= part
    assert union == side and side.bit_count() == (r - 2) * (r + 1)
    assert all(read.bit_count() == r and read & ~side == 0 for read in intervals if not read & failed)
    assert all(sum(1 << ((block * r + j) % n) for j in range(r)) in intervals
               for block in range(1, r))
    return {"r": r, "n": n, "read_contacts_on_side": r,
            "disjoint_global_read_parts": len(parts), "side_size": side.bit_count(),
            "lower_bound": str(Fraction(2 * r - 1, 2 * side.bit_count()))}


def audit(source: Path, out: Path, finite_upper: Path) -> None:
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
        path = source / f"r{r}.json"
        doc = json.loads(path.read_text())
        intervals = {sum(1 << ((start + j) % n) for j in range(r)) for start in range(n)}
        assert n == r * r - 1 and doc["r"] == r and doc["n"] == n
        assert {row["failed"] for row in doc["witnesses"]} == {1 | (1 << d) for d in range(1, r + 1)}
        assert len(doc["witnesses"]) == r
        tests, scenarios = 0, 0
        for row in doc["witnesses"]:
            assert Fraction(row["load"]) == Fraction(2 * r - 1, 2 * (r - 2) * (r + 1))
            labels = range(n) if r <= 9 else (0, n // 2, n - 1)
            for offset in labels:
                for sign in (1, -1):
                    transformed = {**row, "failed": relabel(row["failed"], n, offset, sign)}
                    for phase in ("reads", "writes"):
                        transformed[phase] = {str(relabel(int(q), n, offset, sign)): p
                                              for q, p in row[phase].items()}
                    tests += check(transformed, r, n, intervals)
                    scenarios += 1
        for corruption in ("load", "normalization", "failure", "intersection"):
            bad = deepcopy(doc["witnesses"][0])
            if corruption == "load":
                bad["load"] = "0"
            elif corruption == "normalization":
                q = next(iter(bad["reads"]))
                bad["reads"][q] = str(Fraction(bad["reads"][q]) + 1)
            else:
                q = next(iter(bad["writes"]))
                replacement = 1 if corruption == "failure" else sum(1 << i for i in range(2, r + 2))
                bad["writes"][str(replacement)] = bad["writes"].pop(q)
            try:
                check(bad, r, n, intervals)
            except AssertionError:
                controls.append({"r": r, "corruption": corruption})
            else:
                raise AssertionError("damaged route accepted")
        records.append({**summary, "transformed_routes_checked": scenarios,
                        "global_intersection_tests": tests, "bottleneck": bottleneck(r)})
        hashes[str(path)] = digest(path)
        print(json.dumps(records[-1]), flush=True)
    finite = json.loads((finite_upper / "result.json").read_text())
    for name, expected in finite["sources_sha256"].items():
        assert digest(root / name) == expected
    exact = []
    for summary in finite["records"]:
        r, n = summary["r"], summary["n"]
        path = finite_upper / f"r{r}.json"
        doc = json.loads(path.read_text())
        intervals = {sum(1 << ((start + j) % n) for j in range(r)) for start in range(n)}
        assert {row["failed"] for row in doc["witnesses"]} == {1 | (1 << d) for d in range(1, n // 2 + 1)}
        assert len(doc["witnesses"]) == n // 2
        for row in doc["witnesses"]:
            check(row, r, n, intervals)
        lower = bottleneck(r)
        assert Fraction(lower["lower_bound"]) == max(Fraction(row["load"]) for row in doc["witnesses"])
        assert doc["load"] == summary["load"] == lower["lower_bound"]
        exact.append({**lower, "all_distance_classes_checked": len(doc["witnesses"]),
                      "scope": "Exact optimum with these fixed interval reads, allowing any globally compatible writes."})
        hashes[str(path)] = digest(path)
    snapshots = out / "source"
    snapshots.mkdir()
    for name in ("balanced_mixed_circle_short_arc.py", "balanced_mixed_circle_short_arc_verify.py",
                 "balanced_mixed_circle_verify.py", "balanced_circle.py"):
        hashes[str(root / name)] = digest(root / name)
        shutil.copy2(root / name, snapshots / name)
    result = {"valid": True, "date": "2026-10-12", "short_arc_routes": records,
              "finite_fixed_read_optima": exact, "rejected_corruptions": controls,
              "arbitrary_r_all_placements_proved": False, "global_optimality_proved": False,
              "new_lean_formalization": False, "sha256": hashes}
    (out / "manifest.json").write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--finite-upper", type=Path, default=Path("runs/balanced-mixed-circle-certificates-001"))
    args = parser.parse_args()
    audit(args.source.resolve(), args.out.resolve(), args.finite_upper.resolve())
