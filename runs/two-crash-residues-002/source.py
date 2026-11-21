"""Search finite two-crash extensions; certify accepted routes exactly.

Read candidates are single cyclic orbits of size floor(n/3)+2. Writes
are all triples meeting every read. A rejection excludes only that fixed
family on the whole interval, not all quorum systems at that size.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from pathlib import Path
import time

from lp import minimize_load
from rational_basis_repair import repair_primal
from verify import verify


def rotations(mask, n):
    full, orbit = (1 << n) - 1, set()
    for _ in range(n):
        orbit.add(mask)
        mask = ((mask << 1) & full) | (mask >> (n - 1))
    return sorted(orbit)


def parameters(n):
    k, residue = divmod(n, 3)
    assert k >= 3
    alpha = Fraction(residue + 1, k * k + k + residue - 1)
    return k + 2, alpha


def instance(n, scenarios):
    return {"n": n, "read_capacity": ["1"] * n,
            "write_capacity": ["1"] * n, "scenarios": scenarios}


def exact_route(n, reads, writes, failed, alpha):
    case = instance(n, [{"failed": failed, "read_fraction": str(alpha)}])
    candidate = minimize_load(case, reads, writes)
    assert candidate is not None
    try:
        verify(case, candidate)
    except AssertionError:
        candidate = repair_primal(case, candidate)
        verify(case, candidate)
    return {"instance": case, "candidate": candidate}


def full_certificate(n, reads, writes, alpha):
    scenarios, routes = [], []
    for a in (Fraction(0), alpha / 2, alpha):
        for count in range(3):
            for nodes in combinations(range(n), count):
                failed = sum(1 << i for i in nodes)
                row = exact_route(n, reads, writes, failed, a)
                scenarios.extend(row["instance"]["scenarios"])
                routes.extend(row["candidate"]["scenarios"])
    case = instance(n, scenarios)
    candidate = {"reads": reads, "writes": writes, "scenarios": routes,
                 "load": str(max(Fraction(s["load"]) for s in routes))}
    verify(case, candidate)
    for s in routes:
        a = Fraction(s["read_fraction"])
        target = (3 + (n // 3 - 1) * a) / (n - 2)
        assert Fraction(s["load"]) <= target
    return {"instance": case, "candidate": candidate}


def run(n, seconds, out, interval=False, representatives_only=False):
    out.mkdir(parents=True, exist_ok=False)
    started = time.monotonic()
    rank, alpha = parameters(n)
    seeds = ([(1 << rank) - 1] if interval else
             sorted({min(rotations(sum(1 << i for i in q), n))
                     for q in combinations(range(n), rank)}))
    triples = [sum(1 << i for i in q) for q in combinations(range(n), 3)]
    failures = [1 | (1 << distance) for distance in range(1, n // 2 + 1)]
    result = {"n": n, "read_size": rank, "critical_alpha": str(alpha),
              "read_seeds": seeds, "trials": [], "certificate": None,
              "scope": "One cyclic read orbit, all compatible triples; whole interval from zero to the proposed endpoint.",
              "seed_scope": "contiguous interval only" if interval else "all cyclic read seeds",
              "representatives_only": representatives_only,
              "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
    print(json.dumps({"n": n, "seeds": len(seeds), "alpha": str(alpha)}), flush=True)
    for seed in seeds:
        if time.monotonic() - started >= seconds:
            break
        reads = rotations(seed, n)
        writes = [q for q in triples if all(q & r for r in reads)]
        trial = {"seed": seed, "write_count": len(writes)}
        missing = next((f for f in failures
                        if any(not any(not q & f for q in family)
                               for family in (reads, writes))), None)
        if missing is not None:
            trial["unavailable_failure"] = missing
        else:
            accepted = []
            for a in (Fraction(0), alpha):
                for failed in failures:
                    row = exact_route(n, reads, writes, failed, a)
                    target = (3 + (n // 3 - 1) * a) / (n - 2)
                    if Fraction(row["candidate"]["load"]) > target:
                        trial["obstruction"] = row
                        break
                    accepted.append(row)
                if "obstruction" in trial:
                    break
            else:
                if representatives_only:
                    case = instance(n, [s for row in accepted for s in row["instance"]["scenarios"]])
                    candidate = {"reads": reads, "writes": writes,
                                 "scenarios": [s for row in accepted for s in row["candidate"]["scenarios"]],
                                 "load": str(max(Fraction(row["candidate"]["load"]) for row in accepted))}
                    verify(case, candidate)
                    result["certificate"] = {"instance": case, "candidate": candidate}
                else:
                    result["certificate"] = full_certificate(n, reads, writes, alpha)
                result["attaining_seed"] = seed
                trial["attaining"] = True
        result["trials"].append(trial)
        if trial.get("attaining"):
            break
        if len(result["trials"]) % 50 == 0:
            print(json.dumps({"n": n, "trials": len(result["trials"]),
                              "seconds": time.monotonic() - started}), flush=True)
    result["enumeration_complete"] = len(result["trials"]) == len(seeds)
    result["status"] = ("rational_certificate" if result["certificate"] else
                        "tested_seed_class_excluded" if result["enumeration_complete"] else
                        "unresolved")
    result["elapsed_seconds"] = time.monotonic() - started
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"n": n, "status": result["status"],
                      "trials": len(result["trials"]),
                      "seed": result.get("attaining_seed"),
                      "seconds": result["elapsed_seconds"]}), flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, nargs="+", default=[9, 10, 12, 13, 15, 16])
    parser.add_argument("--seconds", type=float, default=120)
    parser.add_argument("--interval", action="store_true")
    parser.add_argument("--representatives-only", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=False)
    (args.out / "source.py").write_bytes(Path(__file__).read_bytes())
    for n in args.nodes:
        run(n, args.seconds, args.out / f"n{n}", args.interval, args.representatives_only)
