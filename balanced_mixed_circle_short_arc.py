"""Optimizer-free routes for failed pairs at cyclic distance at most r.

Reads have size r, writes have size r or r+1, and n=r^2-1. This is
only part of the two-crash construction: distances greater than r are
not covered by this formula.
"""

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from balanced_circle import circle_flow


def route(r: int, distance: int) -> dict:
    assert r >= 5 and 1 <= distance <= r
    n = r * r - 1
    denominator = (r - 2) * (r + 1)
    mixture = Fraction(r - 5, denominator)
    cap = Fraction(2 * r - 1, denominator)
    first = (r - distance) // 2
    failed = {first, first + distance}
    reads = {}
    for block in range(1, r - 1):
        start = block * r + 1
        reads[sum(1 << i for i in range(start, start + r))] = Fraction(r - block, denominator)
    for block in range(2, r):
        start = block * r - 1
        reads[sum(1 << i for i in range(start, start + r))] = Fraction(block, denominator)
    inclusion = [Fraction(0)] * n
    for read, probability in reads.items():
        mask = read
        while mask:
            bit = mask & -mask
            inclusion[bit.bit_length() - 1] += probability
            mask ^= bit
    if distance <= r - 2:
        small_writes = [{j * r for j in range(r)}]
    elif distance == r - 1:
        small_writes = [{1 + j * r for j in range(r)}]
    else:
        small = {1 + j * r for j in range(r)}
        small_writes = [small, {(r - i) % n for i in small}]
    small_inclusion = [mixture * Fraction(sum(i in write for write in small_writes), len(small_writes))
                       for i in range(n)]
    large_inclusion = [cap - inclusion[i] - small_inclusion[i] if i not in failed else Fraction(0)
                       for i in range(n)]
    assert sum(reads.values()) == 1
    assert all(not read & sum(1 << i for i in failed) for read in reads)
    assert all(not write & failed for write in small_writes)
    assert all(0 <= value <= 1 - mixture for value in large_inclusion)
    assert sum(large_inclusion) == (r + 1) * (1 - mixture)
    window = sum(large_inclusion[:r])
    for start in range(n):
        assert window >= 1 - mixture
        window += large_inclusion[(start + r) % n] - large_inclusion[start]
    writes = {}
    if mixture:
        for write in small_writes:
            mask = sum(1 << i for i in write)
            writes[mask] = writes.get(mask, Fraction(0)) + mixture / len(small_writes)
    flow = circle_flow([value / (1 - mixture) for value in large_inclusion], r + 1)
    for mask, mass in flow["weights"].items():
        write = int(mask)
        writes[write] = writes.get(write, Fraction(0)) + (1 - mixture) * Fraction(mass, flow["mass"])

    def rotate(mask: int) -> int:
        result = 0
        while mask:
            bit = mask & -mask
            result |= 1 << ((bit.bit_length() - 1 - first) % n)
            mask ^= bit
        return result

    return {"failed": 1 | (1 << distance), "read_fraction": "1/2",
            "load": str(cap / 2), "smaller_write_probability": str(mixture),
            "reads": {str(rotate(mask)): str(probability) for mask, probability in reads.items()},
            "writes": {str(rotate(mask)): str(probability) for mask, probability in writes.items()}}


def run(ranks: list[int], out: Path) -> None:
    assert __debug__ and not out.exists()
    out.mkdir(parents=True)
    records = []
    for r in ranks:
        witnesses = [route(r, distance) for distance in range(1, r + 1)]
        doc = {"r": r, "n": r * r - 1, "witnesses": witnesses,
               "scope": "Only cyclic crash distances 1 through r; no all-placement upper bound."}
        (out / f"r{r}.json").write_text(json.dumps(doc, indent=2) + "\n")
        records.append({"r": r, "n": doc["n"], "representatives": len(witnesses),
                        "load": witnesses[0]["load"]})
        print(json.dumps(records[-1]), flush=True)
    names = [Path(__file__).name, "balanced_circle.py"]
    hashes = {name: hashlib.sha256(Path(name).read_bytes()).hexdigest() for name in names}
    (out / "result.json").write_text(json.dumps({"records": records, "sources_sha256": hashes,
                                               "all_placements_proved": False}, indent=2) + "\n")


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--r", type=int, nargs="+", required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()
    run(args.r, args.out.resolve())
