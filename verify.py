"""Independent certificate checker. Imports neither synthesis nor LP code."""

import argparse
from fractions import Fraction
import json
from pathlib import Path


if not __debug__:
    raise RuntimeError(
        "Verification requires assertions. Run without -O and unset PYTHONOPTIMIZE."
    )


def verify(instance: dict, candidate: dict) -> dict:
    n = instance["n"]
    universe = set(range(n))

    def nodes(mask: int) -> set[int]:
        assert 0 < mask < 2**n, f"invalid quorum {mask}"
        return {i for i in universe if (mask // 2**i) % 2 == 1}

    reads = {q: nodes(q) for q in candidate["reads"]}
    writes = {q: nodes(q) for q in candidate["writes"]}
    assert reads and writes
    for r in reads.values():
        for w in writes.values():
            assert not r.isdisjoint(w), "disjoint read/write quorums"
    assert len(candidate["scenarios"]) == len(instance["scenarios"])
    loads = []
    for expected, s in zip(instance["scenarios"], candidate["scenarios"], strict=True):
        assert s["failed"] == expected["failed"]
        assert Fraction(s["read_fraction"]) == Fraction(expected["read_fraction"])
        failed = {i for i in universe if (s["failed"] // 2**i) % 2 == 1}
        ps = []
        for kind, family in (("reads", reads), ("writes", writes)):
            p = {int(q): Fraction(v) for q, v in s[kind].items()}
            assert p and sum(p.values()) == 1, "probabilities do not sum to one"
            assert all(v >= 0 for v in p.values()), "negative probability"
            assert all(q in family for q in p), "unknown quorum"
            assert all(family[q].isdisjoint(failed) for q in p), "access to failed node"
            ps.append(p)
        alpha = Fraction(s["read_fraction"])
        node_load = [
            alpha * sum(v for q, v in ps[0].items() if i in reads[q])
            / Fraction(instance["read_capacity"][i])
            + (1 - alpha) * sum(v for q, v in ps[1].items() if i in writes[q])
            / Fraction(instance["write_capacity"][i]) for i in universe
        ]
        load = Fraction(s["load"])
        assert max(node_load) == load, "wrong exact primal load"
        d = s["dual"]
        weights = [Fraction(v) for v in d["nodes"]]
        assert len(weights) == n and all(v >= 0 for v in weights)
        assert sum(weights) <= 1, "dual node weights exceed one"
        u, v = Fraction(d["read"]), Fraction(d["write"])
        for q, members in reads.items():
            if members.isdisjoint(failed):
                assert sum(weights[i] * alpha / Fraction(instance["read_capacity"][i])
                           for i in members) >= u, "invalid read dual"
        for q, members in writes.items():
            if members.isdisjoint(failed):
                assert sum(weights[i] * (1 - alpha) / Fraction(instance["write_capacity"][i])
                           for i in members) >= v, "invalid write dual"
        assert u + v == load, "primal and dual objectives differ"
        loads.append(load)
    assert max(loads) == Fraction(candidate["load"])
    return {"valid": True, "exact_load": str(max(loads)),
            "intersection_pairs": len(reads) * len(writes), "scenarios": len(loads)}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("certificate", type=Path)
    args = parser.parse_args()
    doc = json.loads(args.certificate.read_text())
    print(json.dumps(verify(doc["instance"], doc["candidate"]), indent=2))
