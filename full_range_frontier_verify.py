#!/usr/bin/env python3
"""Finite, exact checks of the paper's full-range load bounds.

Standard library only. Every assertion uses exact rational arithmetic;
floating point is used only for the reported ratio tables.

Part K (known failures): for every failed set of size at most f, rebuild the
tiled read route and the systematically sampled write route, then check
global cross-intersection, failure avoidance, normalization and the stated
load bound.

Part P (proactive contacts): rebuild interval read contacts and comb write
contacts, check that every pair shares at least 2f+1 servers, that deleting
any f servers from either side keeps the pair intersecting, and the load.
Also check the rounded comb size behind the limit statement: whenever
n >= 2d and 4d(1-alpha) <= alpha*n and alpha*d <= (1-alpha)*n, the size
q = ceil(sqrt(alpha*d*n/(1-alpha))) is admissible and the load exceeds
2*sqrt(d*alpha*(1-alpha)/n) by at most (alpha*d + 1 - alpha)/n.

Part B (bound relations): check the lower bounds against the constructions,
against the exact corner theorems, and the uniform constant.
"""

from __future__ import annotations

import argparse
import hashlib
import itertools
import json
import math
import pathlib
from collections import Counter
from fractions import Fraction as Fr

if not __debug__:
    raise RuntimeError(
        "Verification requires assertions. Run without -O and unset PYTHONOPTIMIZE."
    )

ALPHAS = [Fr(a, 40) for a in range(0, 41)]


def ceil_div(a: int, b: int) -> int:
    return -(-a // b)


def interval_family(n: int, rho: int) -> list[frozenset[int]]:
    return [frozenset((s + j) % n for j in range(rho)) for s in range(n)]


def live_arcs(n: int, failed: frozenset[int]) -> list[list[int]]:
    """Maximal cyclic runs of live servers. Requires at least one failure."""
    start = min(failed)
    arcs: list[list[int]] = []
    run: list[int] = []
    for step in range(1, n + 1):
        i = (start + step) % n
        if i in failed:
            arcs.append(run)
            run = []
        else:
            run.append(i)
    assert not run
    return arcs


def known_tiles(n: int, rho: int, failed: frozenset[int]) -> list[frozenset[int]]:
    tiles = []
    for arc in live_arcs(n, failed):
        for j in range(len(arc) // rho):
            tiles.append(frozenset(arc[j * rho:(j + 1) * rho]))
    return tiles


def sampled_writes(n: int, q: int, h: int, weights: list[int]) -> Counter:
    """Weighted systematic sampling (the manuscript's Lemma 5)."""
    assert sum(weights) == q * h and all(0 <= a <= h for a in weights)
    owner = [i for i in range(n) for _ in range(weights[i])]
    out: Counter = Counter()
    for t in range(h):
        w = frozenset(owner[t + j * h] for j in range(q))
        assert len(w) == q
        out[w] += 1
    return out


def n_tiles_bound(m: int, f: int, rho: int) -> int:
    return ceil_div(m - f * (rho - 1), rho)


def known_upper(m: int, f: int, rho: int, alpha: Fr) -> Fr:
    big_n = n_tiles_bound(m, f, rho)
    q = ceil_div(m, rho - f)
    return alpha / big_n + (1 - alpha) * Fr(q, m)


def valid_rho(n: int, f: int) -> list[int]:
    m = n - f
    return [r for r in range(f + 1, n + 1) if m - f * (r - 1) >= 1]


def pad(n: int, f: int, failed: frozenset[int]) -> frozenset[int]:
    extra = [i for i in range(n) if i not in failed][: f - len(failed)]
    return failed | frozenset(extra)


def check_known(n: int, f: int, counts: Counter) -> None:
    m = n - f
    for rho in valid_rho(n, f):
        reads = set(interval_family(n, rho))
        read_list = list(reads)
        q = ceil_div(m, rho - f)
        assert f + 1 <= q <= m, (n, f, rho, q)
        nb = n_tiles_bound(m, f, rho)
        assert nb >= 1
        hit_cache: dict[frozenset[int], bool] = {}
        for size in range(0, f + 1):
            for combo in itertools.combinations(range(n), size):
                actual = frozenset(combo)
                failed = pad(n, f, actual)
                assert len(failed) == f and actual <= failed
                tiles = known_tiles(n, rho, failed)
                assert len(tiles) >= nb
                for t in tiles:
                    assert t in reads and not (t & failed)
                weights = [0 if i in failed else q for i in range(n)]
                writes = sampled_writes(n, q, m, weights)
                for w in writes:
                    assert not (w & failed)
                    ok = hit_cache.get(w)
                    if ok is None:
                        ok = all(w & r for r in read_list)
                        hit_cache[w] = ok
                    assert ok, (n, f, rho, sorted(failed), sorted(w))
                x = Counter()
                for t in tiles:
                    for i in t:
                        x[i] += 1
                y = Counter()
                for w, c in writes.items():
                    for i in w:
                        y[i] += c
                assert sum(writes.values()) == m
                for i in range(n):
                    if i in failed:
                        assert x[i] == 0 and y[i] == 0
                    else:
                        assert Fr(y[i], m) == Fr(q, m)
                        assert Fr(x[i], len(tiles)) <= Fr(1, nb)
                for alpha in ALPHAS:
                    worst = max(
                        alpha * Fr(x[i], len(tiles)) + (1 - alpha) * Fr(y[i], m)
                        for i in range(n) if i not in actual
                    )
                    assert worst <= known_upper(m, f, rho, alpha)
                    counts["known_load_checks"] += 1
                counts["known_failed_sets"] += 1
        counts["known_designs"] += 1
        counts["known_distinct_writes"] += len(hit_cache)


def comb(n: int, q: int) -> frozenset[int]:
    return frozenset((j * n) // q for j in range(q))


def max_gap(n: int, pts: frozenset[int]) -> int:
    s = sorted(pts)
    return max((s[(j + 1) % len(s)] - s[j]) % n or n for j in range(len(s)))


def proactive_upper(n: int, d: int, q: int, alpha: Fr) -> Fr:
    return (alpha * d * ceil_div(n, q) + (1 - alpha) * q) / n


def check_proactive(n: int, f: int, counts: Counter, deletions: bool) -> None:
    d = 2 * f + 1
    for q in range(d, n + 1):
        gap = ceil_div(n, q)
        rho = d * gap
        if rho > n:
            continue
        base = comb(n, q)
        assert len(base) == q and max_gap(n, base) == gap
        combs = {frozenset((i + s) % n for i in base) for s in range(n)}
        reads = interval_family(n, rho)
        for a in reads:
            for b in combs:
                common = a & b
                assert len(common) >= d
                counts["proactive_pairs"] += 1
                if deletions and len(common) <= d + 1:
                    for fa in itertools.combinations(sorted(common), min(f, len(common))):
                        rest = common - frozenset(fa)
                        for fb in itertools.combinations(sorted(rest), min(f, len(rest))):
                            assert rest - frozenset(fb)
                            counts["proactive_deletions"] += 1
        # rotation-uniform loads are rho/n and q/n at every server
        x = Counter(i for a in reads for i in a)
        assert all(Fr(x[i], n) == Fr(rho, n) for i in range(n))
        orbit = [frozenset((i + s) % n for i in base) for s in range(n)]
        y = Counter(i for b in orbit for i in b)
        assert all(Fr(y[i], n) == Fr(q, n) for i in range(n))
        for alpha in ALPHAS:
            up = proactive_upper(n, d, q, alpha)
            assert up == alpha * Fr(rho, n) + (1 - alpha) * Fr(q, n)
            assert up >= Fr(d, n)
            assert up * up * n >= 4 * d * alpha * (1 - alpha)
        if n % q == 0:
            alpha_q = Fr(q * q, q * q + d * n)
            val = proactive_upper(n, d, q, alpha_q)
            assert val == Fr(2 * d * q, q * q + d * n)
            assert val * val * n == 4 * d * alpha_q * (1 - alpha_q)
            counts["proactive_exact_points"] += 1
        counts["proactive_designs"] += 1


def check_proactive_rounding(counts: Counter) -> None:
    """Rounded comb size used for the limit of the proactive optimum."""
    alphas = [Fr(a, 200) for a in range(1, 200)]
    for f in (1, 2, 3, 4):
        d = 2 * f + 1
        for n in range(2 * d, 2 * d + 300):
            for alpha in alphas:
                if alpha * n < 4 * d * (1 - alpha) or alpha * d > (1 - alpha) * n:
                    continue
                target = alpha * d * n / (1 - alpha)      # q0 squared
                q = math.isqrt(math.floor(target))
                while q * q < target:
                    q += 1
                assert (q - 1) * (q - 1) < target <= q * q
                assert 2 * d <= q <= n, (n, f, alpha, q)
                gap = ceil_div(n, q)
                assert d * gap <= n, (n, f, alpha, q)
                excess = alpha * d * (gap - 1) + (1 - alpha) * (q - 1)
                assert excess >= 0
                assert excess * excess <= 4 * d * alpha * (1 - alpha) * n
                assert (proactive_upper(n, d, q, alpha)
                        == (excess + alpha * d + 1 - alpha) / n)
                counts["proactive_rounding_checks"] += 1


def best_known_upper(m: int, f: int, alpha: Fr, rhos: list[int]) -> Fr:
    return min(known_upper(m, f, r, alpha) for r in rhos)


def check_bounds(counts: Counter) -> dict:
    worst_const = Fr(0)
    for f in (1, 2, 3, 4):
        for n in range(f * f + f + 1, 16 * f * f + f + 140):
            m = n - f
            rhos = valid_rho(n, f)
            for alpha in ALPHAS:
                up = min(best_known_upper(m, f, alpha, rhos),
                         best_known_upper(m, f, 1 - alpha, rhos))
                assert up >= Fr(f + 1, m)
                assert up * up * m >= 4 * alpha * (1 - alpha)
                counts["bound_order_checks"] += 1
                if m >= 16 * f * f:
                    beta = alpha * (1 - alpha)
                    ok_corner = up <= 20 * Fr(f + 1, m)
                    ok_mid = up * up * m <= 400 * beta
                    assert ok_corner or ok_mid, (n, f, alpha)
                    ratio_sq = min((up * m / (f + 1)) ** 2,
                                   up * up * m / beta if beta else Fr(10 ** 9))
                    worst_const = max(worst_const, ratio_sq)
                    counts["uniform_constant_checks"] += 1
    # exact corner theorems lie between the bounds
    for f in (1, 2, 3):
        for k in range(f * f + 1, f * f + 40):
            n = (f + 1) * k
            m = n - f
            d_ = (k - 1) * (k + f) + 1
            rhos = valid_rho(n, f)
            for j in range(0, 5):
                alpha = Fr(j, 4 * d_)
                exact = (f + 1 + (k - 1) * alpha) / m
                assert exact >= Fr(f + 1, m)
                assert exact * exact * m >= 4 * alpha * (1 - alpha)
                assert exact <= best_known_upper(m, f, alpha, rhos)
                counts["corner_theorem_checks"] += 1
    for n in range(9, 200):
        k, r = divmod(n, 3)
        m = n - 2
        rhos = valid_rho(n, 2)
        top = Fr(r + 1, k * k + k + r - 1)
        for j in range(0, 5):
            alpha = top * j / 4
            exact = (3 + (k - 1) * alpha) / m
            assert exact * exact * m >= 4 * alpha * (1 - alpha)
            assert exact <= best_known_upper(m, 2, alpha, rhos)
            counts["corner_theorem_checks"] += 1
    return {"uniform_constant_worst_sqrt": math.sqrt(worst_const)}


def ratio_tables() -> dict:
    known = []
    price = []
    for f in (1, 2, 3):
        d = 2 * f + 1
        for n in (10 ** 2, 10 ** 3, 10 ** 4, 10 ** 5, 10 ** 6):
            m = n - f
            for a in (0.01, 0.1, 0.5):
                lb = 2 * math.sqrt(a * (1 - a) / m)
                rho0 = math.sqrt(m * (1 - a) / a)
                best = None
                for rho in range(max(f + 1, int(rho0) - 60), int(rho0) + f + 62):
                    if m - f * (rho - 1) < 1:
                        continue
                    nb = ceil_div(m - f * (rho - 1), rho)
                    q = ceil_div(m, rho - f)
                    u = a / nb + (1 - a) * q / m
                    best = u if best is None else min(best, u)
                q0 = math.sqrt(a * d * n / (1 - a))
                pbest = None
                for q in range(max(d, int(q0) - 60), int(q0) + 62):
                    if d * ceil_div(n, q) > n:
                        continue
                    u = (a * d * ceil_div(n, q) + (1 - a) * q) / n
                    pbest = u if pbest is None else min(pbest, u)
                plb = max(d / n, 2 * math.sqrt(d * a * (1 - a) / n))
                row = {"f": f, "n": n, "alpha": a}
                if best is not None:
                    known.append({**row, "lower": lb, "upper": best,
                                  "upper_over_lower": best / lb})
                if best is not None and pbest is not None:
                    price.append({**row, "proactive_lower": plb,
                                  "proactive_upper": pbest,
                                  "known_upper": best,
                                  "guaranteed_ratio": plb / best,
                                  "limit": math.sqrt(d)})
    return {"known": known, "price_of_unknown_failures": price}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--out", required=True)
    ap.add_argument("--quick", action="store_true")
    args = ap.parse_args()

    counts: Counter = Counter()
    known_ranges = {1: range(3, 25), 2: range(5, 19), 3: range(7, 15)}
    pro_ranges = {1: range(3, 49), 2: range(5, 49), 3: range(7, 49)}
    if args.quick:
        known_ranges = {1: range(3, 12), 2: range(5, 11)}
        pro_ranges = {1: range(3, 20), 2: range(5, 20)}
    for f, rng in known_ranges.items():
        for n in rng:
            check_known(n, f, counts)
    for f, rng in pro_ranges.items():
        for n in rng:
            check_proactive(n, f, counts, deletions=n <= 24)
    check_proactive_rounding(counts)
    extra = check_bounds(counts)
    tables = ratio_tables()

    here = pathlib.Path(__file__).resolve()
    note = here.with_name("full_range_frontier.md")
    result = {
        "status": "pass",
        "counts": dict(sorted(counts.items())),
        "known_ranges": {str(f): [r.start, r.stop - 1] for f, r in known_ranges.items()},
        "proactive_ranges": {str(f): [r.start, r.stop - 1] for f, r in pro_ranges.items()},
        **extra,
        "tables": tables,
        "sha256": {
            here.name: hashlib.sha256(here.read_bytes()).hexdigest(),
            note.name: hashlib.sha256(note.read_bytes()).hexdigest() if note.exists() else None,
        },
    }
    out = pathlib.Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    (out / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: v for k, v in result.items() if k != "tables"}, indent=2))


if __name__ == "__main__":
    main()
