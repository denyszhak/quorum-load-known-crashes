"""Optimizer-free mixed-circle routes after any two crashes, r>=5.

The closed formulas and their written proof are in
balanced_mixed_circle_all_proof.md. Actual writes are exported so a
separate checker can verify every claimed finite load directly.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from balanced_circle import circle_flow
from balanced_mixed_circle_short_arc import route as short_route


def route(r: int, distance: int) -> dict:
    assert r >= 5
    n = r * r - 1
    assert 1 <= distance <= n // 2
    if distance <= r:
        return {**short_route(r, distance), "case": "close"}
    denominator = (r - 2) * (r + 1)
    mixture = Fraction(r - 5, denominator)
    cap = Fraction(2 * r - 1, denominator)
    failed = {0, distance}
    arcs = [list(range(1, distance)), list(range(distance + 1, n))]
    remainders = [len(arc) % r for arc in arcs]
    reads = {}

    def add(arc: list[int], start: int, probability: Fraction) -> None:
        selected = arc[start:start + r]
        assert len(selected) == r and probability > 0
        read = sum(1 << i for i in selected)
        reads[read] = reads.get(read, Fraction(0)) + probability

    if sum(remainders) == r - 3:
        kind = "buffered"
        blocks = []
        for arc, remainder in zip(arcs, remainders, strict=True):
            count = len(arc) // r
            offset = remainder // 2
            for j in range(count):
                start = offset + j * r
                low = start == 0 or start + r == len(arc)
                blocks.append((arc, start, low))
        assert len(blocks) == r - 1
        low_count = sum(low for _, _, low in blocks)
        assert low_count <= 2
        low = (1 - mixture) / (r - 1)
        high = (1 - low_count * low) / (r - 1 - low_count)
        for arc, start, is_low in blocks:
            add(arc, start, low if is_low else high)
        small = {1 + j * r for j in range(r)}
        if small & failed:
            small = {n - 1 - j * r for j in range(r)}
    else:
        kind = "overlapping"
        assert sorted(remainders) == [r - 2, r - 1]
        counts = [(len(arc) + r - 1) // r for arc in arcs]
        assert sum(counts) == r and min(counts) >= 2
        for arc, count in zip(arcs, counts, strict=True):
            deficit = count * r - len(arc)
            assert deficit in (1, 2)
            shift = Fraction(r - count + 1, 2)
            for j in range(count - 1):
                add(arc, j * r, (count - 1 - j + shift) / denominator)
            for j in range(1, count):
                add(arc, j * r - deficit, (j + shift) / denominator)
        small = {n - 1 - j * r for j in range(r)}
        assert counts[0] <= counts[1]
    assert not small & failed and len(small) == r
    assert sum(reads.values()) == 1
    inclusion = [Fraction(0)] * n
    for read, probability in reads.items():
        mask = read
        while mask:
            bit = mask & -mask
            inclusion[bit.bit_length() - 1] += probability
            mask ^= bit
    residual = [cap - inclusion[i] - mixture * int(i in small) if i not in failed else Fraction(0)
                for i in range(n)]
    assert all(0 <= value <= 1 - mixture for value in residual)
    assert sum(residual) == (r + 1) * (1 - mixture)
    window = sum(residual[:r])
    for start in range(n):
        assert window >= 1 - mixture, (r, distance, start, window, 1 - mixture)
        window += residual[(start + r) % n] - residual[start]
    writes = {}
    if mixture:
        writes[sum(1 << i for i in small)] = mixture
    flow = circle_flow([value / (1 - mixture) for value in residual], r + 1)
    for mask, mass in flow["weights"].items():
        write = int(mask)
        writes[write] = writes.get(write, Fraction(0)) + (1 - mixture) * Fraction(mass, flow["mass"])
    return {"failed": 1 | (1 << distance), "read_fraction": "1/2", "load": str(cap / 2),
            "smaller_write_probability": str(mixture), "case": kind,
            "reads": {str(mask): str(probability) for mask, probability in reads.items()},
            "writes": {str(mask): str(probability) for mask, probability in writes.items()}}


def run(ranks: list[int], out: Path) -> None:
    assert __debug__ and not out.exists()
    out.mkdir(parents=True)
    records = []
    for r in ranks:
        n = r * r - 1
        witnesses = [route(r, distance) for distance in range(1, n // 2 + 1)]
        bound = Fraction(2 * r - 1, 2 * (r - 2) * (r + 1))
        doc = {"r": r, "n": n, "load": str(bound), "witnesses": witnesses,
               "scope": "Explicit routes for all distance classes; written arbitrary-r proof, not full Lean."}
        (out / f"r{r}.json").write_text(json.dumps(doc, indent=2) + "\n")
        summary = {"r": r, "n": n, "load": str(bound), "representatives": len(witnesses),
                   "case_counts": {kind: sum(row["case"] == kind for row in witnesses)
                                   for kind in ("close", "buffered", "overlapping")}}
        records.append(summary)
        print(json.dumps(summary), flush=True)
    names = [Path(__file__).name, "balanced_mixed_circle_short_arc.py", "balanced_circle.py"]
    hashes = {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in names}
    (out / "result.json").write_text(json.dumps({"records": records, "sources_sha256": hashes,
                                               "full_lean_formalization": False}, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--r", type=int, nargs="+", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.r, args.out.resolve())
