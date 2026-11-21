"""Exact independent check of finite gadgets and their block expansions.

This checker uses only the supplied certificates. The paper's cyclic
insertion lemma extends the finite cases to arbitrary cluster sizes.
The finite expansion checks exercise the implementation of that lemma.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path


if not __debug__:
    raise RuntimeError(
        "Verification requires assertions. Run without -O and unset PYTHONOPTIMIZE."
    )


def members(mask: int, n: int) -> set[int]:
    assert 0 < mask < 1 << n
    return {i for i in range(n) if mask & (1 << i)}


def triples(n: int) -> dict[tuple[int, int], int]:
    result = {(start, step): sum(1 << ((start + step * j) % n) for j in range(3))
              for start in range(n) for step in (1, 2)}
    assert len(set(result.values())) == 2 * n
    return result


def check_case(case: dict, retained: int) -> None:
    a, b, k, n = (case[key] for key in ("arc_a", "arc_b", "k", "n"))
    assert 0 <= a <= b <= retained + 2 and a + b == 3 * k and k >= 3
    assert n == 3 * k + 2 and case["distance"] == a + 1
    assert case["pure_status"] == case["critical_status"] == 0
    assert case["mode"] == "periodic flow"
    failed = {0, a + 1}
    cuts = case["cuts"]
    eligible = ([range(1, a + 1)] if a >= retained else [])
    eligible += ([range(a + 2, n)] if b >= retained else [])
    assert len(cuts) == len(eligible)
    for cut, arc in zip(cuts, eligible, strict=True):
        assert set(range(cut - 4, cut + 7)) <= set(arc)
    all_writes = triples(n)
    read_counts = {int(q): int(count) for q, count in case["read_counts"].items()}
    assert all(count > 0 and count == case["read_counts"][str(q)] for q, count in read_counts.items())
    assert sum(read_counts.values()) == 3
    read_sets = {q: members(q, n) for q in read_counts}
    for read in read_sets.values():
        assert len(read) == k + 2 and read.isdisjoint(failed)
        assert all(read & members(q, n) for q in all_writes.values())
        for cut in cuts:
            window = set(range(cut - 4, cut + 4))
            assert read & window in [{i for i in window if (i - cut) % 3 == phase}
                                     for phase in range(3)]
    counts = [sum(count for q, count in read_counts.items() if i in read_sets[q]) for i in range(n)]
    for cut in cuts:
        assert all(counts[i] == 1 for i in range(cut - 4, cut + 4))
    for label in ("critical_write_flow", "uniform_write_flow"):
        flow = {int(q): Fraction(value) for q, value in case[label].items()}
        assert flow and all(value >= 0 for value in flow.values())
        assert set(flow) <= set(all_writes.values())
        assert all(members(q, n).isdisjoint(failed) for q in flow)
        for i in range(n):
            degree = sum(value for q, value in flow.items() if i in members(q, n))
            expected = 0 if i in failed else (1 if label == "uniform_write_flow" else k + 2 - counts[i])
            assert degree == expected, (label, i, degree, expected)
        assert sum(flow.values()) == (k if label == "uniform_write_flow" else (k - 1) * (k + 2))
        for cut in cuts:
            for start in range(cut - 4, cut):
                for step in (1, 2):
                    assert flow.get(all_writes[start, step], 0) == flow.get(all_writes[start + 3, step], 0)


def expand(case: dict, retained: int, extra_a: int, extra_b: int) -> dict:
    assert extra_a >= 0 and extra_b >= 0
    assert not extra_a or case["arc_a"] >= retained
    assert not extra_b or case["arc_b"] >= retained
    amounts = ([extra_a] if case["arc_a"] >= retained else [])
    amounts += ([extra_b] if case["arc_b"] >= retained else [])
    insertions = [(cut, 3 * amount) for cut, amount in zip(case["cuts"], amounts, strict=True)]
    old_n, delta = case["n"], extra_a + extra_b
    n, k = old_n + 3 * delta, case["k"] + delta

    def mapped(i: int) -> int:
        return i + sum(length for cut, length in insertions if cut <= i)

    provenance = {mapped(i): i for i in range(old_n)}
    for cut, length in insertions:
        new_start = cut + sum(other_length for other_cut, other_length in insertions if other_cut < cut)
        for j in range(length):
            provenance[new_start + j] = cut + j % 3
    assert set(provenance) == set(range(n))
    expanded_reads = {}
    for old_q, count in case["read_counts"].items():
        old = members(int(old_q), old_n)
        read = {i for i, original in provenance.items() if original in old}
        expanded_reads[sum(1 << i for i in read)] = count
    old_writes, new_writes = triples(old_n), triples(n)
    critical = {int(q): Fraction(value) for q, value in case["critical_write_flow"].items()}
    uniform = {int(q): Fraction(value) for q, value in case["uniform_write_flow"].items()}
    expanded_flow = {}
    expanded_uniform = {}
    for (start, step), q in new_writes.items():
        original = old_writes[provenance[start], step]
        weight = critical.get(original, 0) + delta * uniform.get(original, 0)
        if weight:
            expanded_flow[q] = weight
        if uniform.get(original, 0):
            expanded_uniform[q] = uniform[original]
    failed = {mapped(0), mapped(case["distance"])}
    read_sets = {q: members(q, n) for q in expanded_reads}
    write_sets = {q: members(q, n) for q in new_writes.values()}
    for q, count in expanded_reads.items():
        read = read_sets[q]
        assert len(read) == k + 2 and read.isdisjoint(failed)
        assert all(read & write for write in write_sets.values())
    assert all(write_sets[q].isdisjoint(failed) for q in expanded_flow)
    assert all(weight >= 0 for weight in expanded_flow.values())
    assert sum(expanded_flow.values()) == (k - 1) * (k + 2)
    assert sum(expanded_uniform.values()) == k
    for i in range(n):
        read_degree = sum(count for q, count in expanded_reads.items() if i in read_sets[q])
        write_degree = sum(weight for q, weight in expanded_flow.items() if i in write_sets[q])
        uniform_degree = sum(weight for q, weight in expanded_uniform.items() if i in write_sets[q])
        assert read_degree + write_degree == (0 if i in failed else k + 2)
        assert uniform_degree == (0 if i in failed else 1)
    return {"n": n, "k": k, "failed": sorted(failed),
            "read_counts": {str(q): count for q, count in expanded_reads.items()},
            "scaled_write_weights": {str(q): str(weight) for q, weight in expanded_flow.items()},
            "uniform_write_flow": {str(q): str(weight) for q, weight in expanded_uniform.items()}}


def verify(source: Path, out: Path) -> dict:
    doc = json.loads(source.read_text())
    retained = doc["retained"]
    assert retained >= 12 and retained % 3 == 0
    cases = doc["cases"]
    keyed = {(case["arc_a"], case["arc_b"]): case for case in cases}
    expected = {(a, b) for a in range(retained + 3) for b in range(a, retained + 3)
                if (a + b) % 3 == 0 and a + b >= 9}
    assert len(cases) == len(keyed) and set(keyed) == expected
    controls = []
    for case in cases:
        check_case(case, retained)
        for extra_a, extra_b in ((0, 0), (1, 0), (0, 1), (1, 1), (7, 11), (20, 20)):
            if extra_a and case["arc_a"] < retained or extra_b and case["arc_b"] < retained:
                continue
            expanded = expand(case, retained, extra_a, extra_b)
            controls.append({"base_arcs": [case["arc_a"], case["arc_b"]],
                             "added_blocks": [extra_a, extra_b], "n": expanded["n"]})
    # Every distance through 62 nodes is separately reduced and reconstructed.
    distances = []
    for k in range(3, 21):
        for a in range(3 * k // 2 + 1):
            b = 3 * k - a
            reduced = [length if length < retained else retained + length % 3 for length in (a, b)]
            additions = [(length - small) // 3 for length, small in zip((a, b), reduced)]
            if reduced[0] > reduced[1]:
                reduced.reverse()
                additions.reverse()
            case = keyed[tuple(reduced)]
            expanded = expand(case, retained, *additions)
            assert expanded["n"] == 3 * k + 2
            assert sorted((expanded["failed"][1] - 1, expanded["n"] - expanded["failed"][1] - 1)) == [a, b]
            distances.append({"n": expanded["n"], "arc_a": a, "arc_b": b,
                              "base_arcs": reduced, "added_blocks": additions})
    result = {"source": str(source), "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
              "valid": True, "retained_arc_length": retained, "base_cases": len(cases),
              "expansion_controls": len(controls), "distance_controls": len(distances),
              "scope": "finite rational gadgets plus controls for the unbounded insertion lemma",
              "controls": controls, "distances": distances}
    out.mkdir(parents=True, exist_ok=True)
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: value for key, value in result.items() if key not in ("controls", "distances")}), flush=True)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    verify(args.source, args.out)
