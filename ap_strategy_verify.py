"""Independent rational check of exported AP-cycle strategies."""

import argparse
from fractions import Fraction
from itertools import combinations
import json
from pathlib import Path


if not __debug__:
    raise RuntimeError(
        "Verification requires assertions. Run without -O and unset PYTHONOPTIMIZE."
    )


def verify(doc: dict, all_failures: bool = False) -> dict:
    scenarios = doc["scenarios"]
    assert scenarios
    n = scenarios[0]["n"]
    assert n >= 11 and n % 3 == 2
    k = (n - 2) // 3
    universe = set(range(n))
    writes = {frozenset((start + step * j) % n for j in range(3))
              for start in range(n) for step in (1, 2)}
    assert len(writes) == 2 * n

    def nodes(mask: int) -> frozenset[int]:
        assert 0 < mask < 1 << n
        return frozenset(i for i in universe if mask // (1 << i) % 2)

    checked_reads, failures = set(), []
    for scenario in scenarios:
        assert scenario["n"] == n
        failed = set(scenario["failed_nodes"])
        padded = set(scenario["padded_failed_nodes"])
        assert len(failed) == len(scenario["failed_nodes"]) <= 2
        assert len(padded) == len(scenario["padded_failed_nodes"]) == 2
        assert failed <= padded <= universe
        failures.append(frozenset(failed))
        alpha = Fraction(scenario["read_fraction"])
        critical = Fraction(3, k * k + k + 1)
        assert Fraction(scenario["critical_read_fraction"]) == critical
        assert 0 <= alpha <= critical
        probabilities = []
        for kind in ("reads", "writes"):
            distribution = {nodes(int(q)): Fraction(p) for q, p in scenario[kind].items()}
            assert distribution and sum(distribution.values()) == 1
            assert all(p >= 0 and quorum.isdisjoint(padded) for quorum, p in distribution.items())
            if kind == "writes":
                assert set(distribution) <= writes
            else:
                for read in distribution:
                    assert len(read) == k + 2
                    if read not in checked_reads:
                        assert all(read & write for write in writes)
                        checked_reads.add(read)
            probabilities.append(distribution)
        target = (3 + (k - 1) * alpha) / (3 * k)
        assert Fraction(scenario["load"]) == target
        for i in universe:
            load = alpha * sum(p for quorum, p in probabilities[0].items() if i in quorum)
            load += (1 - alpha) * sum(p for quorum, p in probabilities[1].items() if i in quorum)
            assert load == (0 if i in padded else target)
    assert len(failures) == len(set(failures))
    if all_failures:
        expected = {frozenset(failed) for count in range(3) for failed in combinations(range(n), count)}
        assert set(failures) == expected
    return {"valid": True, "n": n, "scenarios": len(scenarios),
            "global_read_write_pairs": len(checked_reads) * len(writes),
            "complete_failure_coverage": all_failures}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--all-failures", action="store_true")
    args = parser.parse_args()
    print(json.dumps(verify(json.loads(args.source.read_text()), args.all_failures)))
