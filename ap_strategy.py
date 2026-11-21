"""Generate exact AP-cycle strategies without an optimizer, at any size.

Uses the independently verified finite gadget table and periodic insertion
lemma. This is an access-strategy generator, not a replication protocol.
"""

import argparse
from fractions import Fraction
import hashlib
from itertools import combinations
import json
from pathlib import Path

from ap_gadget_verify import check_case, expand


def load_gadgets(source: Path) -> tuple[int, dict]:
    doc = json.loads(source.read_text())
    retained = doc["retained"]
    cases = {(case["arc_a"], case["arc_b"]): case for case in doc["cases"]}
    expected = {(a, b) for a in range(retained + 3) for b in range(a, retained + 3)
                if (a + b) % 3 == 0 and a + b >= 9}
    assert len(cases) == len(doc["cases"]) and set(cases) == expected
    for case in cases.values():
        check_case(case, retained)
    return retained, cases


def strategy(n: int, failed_nodes: list[int], alpha: Fraction,
             retained: int, cases: dict) -> dict:
    assert n >= 11 and n % 3 == 2
    assert len(set(failed_nodes)) == len(failed_nodes) <= 2
    assert all(0 <= i < n for i in failed_nodes)
    k, denominator = (n - 2) // 3, ((n - 2) // 3) ** 2 + (n - 2) // 3 + 1
    critical = Fraction(3, denominator)
    assert 0 <= alpha <= critical
    padded = set(failed_nodes)
    for i in range(n):
        if len(padded) == 2:
            break
        padded.add(i)
    first, second = sorted(padded)
    arcs = [second - first - 1, n - (second - first) - 1]
    reduced = [length if length < retained else retained + length % 3 for length in arcs]
    additions = [(length - small) // 3 for length, small in zip(arcs, reduced)]
    start = first
    if reduced[0] > reduced[1]:
        reduced.reverse()
        additions.reverse()
        start = second
    expanded = expand(cases[tuple(reduced)], retained, *additions)
    assert expanded["n"] == n

    def rotate(mask: int) -> int:
        return sum(1 << ((i + start) % n) for i in range(n) if mask & (1 << i))

    reads = {rotate(int(q)): Fraction(count, 3) for q, count in expanded["read_counts"].items()}
    t = alpha / critical
    critical_flow = {int(q): Fraction(weight) for q, weight in expanded["scaled_write_weights"].items()}
    pure_flow = {int(q): Fraction(weight) for q, weight in expanded["uniform_write_flow"].items()}
    writes = {}
    for q in critical_flow.keys() | pure_flow.keys():
        phase_mass = alpha * critical_flow.get(q, 0) / 3 + (1 - t) * pure_flow.get(q, 0) / k
        if phase_mass:
            writes[rotate(q)] = phase_mass / (1 - alpha)
    assert sum(reads.values()) == sum(writes.values()) == 1
    assert all(value >= 0 for value in list(reads.values()) + list(writes.values()))
    failed_mask = sum(1 << i for i in padded)
    assert all(not q & failed_mask for q in reads.keys() | writes.keys())
    target = Fraction(3 + (k - 1) * alpha, 3 * k)
    loads = [alpha * sum(p for q, p in reads.items() if q & (1 << i))
             + (1 - alpha) * sum(p for q, p in writes.items() if q & (1 << i)) for i in range(n)]
    assert all(load == (0 if i in padded else target) for i, load in enumerate(loads))
    return {"n": n, "failed_nodes": sorted(failed_nodes), "padded_failed_nodes": sorted(padded),
            "read_fraction": str(alpha), "critical_read_fraction": str(critical),
            "base_arcs": reduced, "added_blocks": additions, "load": str(target),
            "reads": {str(q): str(p) for q, p in reads.items()},
            "writes": {str(q): str(p) for q, p in writes.items()}}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--nodes", type=int, required=True)
    parser.add_argument("--failed", type=int, nargs="*", default=[])
    parser.add_argument("--alpha", type=Fraction)
    parser.add_argument("--gadgets", type=Path, default=Path(__file__).resolve().parent / "runs/ap-gadgets-006/result.json")
    parser.add_argument("--all-failures", action="store_true")
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    retained, cases = load_gadgets(args.gadgets)
    k = (args.nodes - 2) // 3
    alpha = args.alpha if args.alpha is not None else Fraction(3, k * k + k + 1)
    failures = [list(failed) for count in range(3) for failed in combinations(range(args.nodes), count)] if args.all_failures else [args.failed]
    records = [strategy(args.nodes, failed, alpha, retained, cases) for failed in failures]
    output = {"gadgets": str(args.gadgets), "gadgets_sha256": hashlib.sha256(args.gadgets.read_bytes()).hexdigest(),
              "construction": "fixed AP1/AP2 writes and all rank-(k+2) transversals",
              "scenarios": records, "scope": "exact access strategies; no protocol or throughput claim"}
    args.out.mkdir(parents=True, exist_ok=True)
    (args.out / "result.json").write_text(json.dumps(output, indent=2) + "\n")
    print(json.dumps({"n": args.nodes, "scenarios": len(records), "alpha": str(alpha),
                      "load": records[0]["load"]}), flush=True)
