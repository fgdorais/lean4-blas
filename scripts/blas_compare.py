#!/usr/bin/env python3
"""Compare `lake exe bench` with C BLAS implementations.

Usage: blas_compare.py LEAN.tsv NAME=OTHER.tsv...

LEAN.tsv holds the `lake exe bench --tsv` output, and each OTHER.tsv the `cblas_bench` output of
one implementation, which is labeled NAME. Each file may hold several runs, of which the fastest
time is kept. The table shows each time in milliseconds, or GFLOP/s where the operation count is
known, and the ratio of the implementation's speed to `BLAS`'s: 2.0 means it is twice as fast.
`gemm` and `gemmNaive` are both compared with the implementation's `gemm`.
"""

import re
import sys


def load(path):
    times = {}
    order = []
    with open(path) as f:
        for line in f:
            name, _, ms = line.rstrip("\n").partition("\t")
            if not ms:
                continue
            if name not in times:
                order.append(name)
                times[name] = float(ms)
            else:
                times[name] = min(times[name], float(ms))
    return order, times


def flops(name):
    """The floating-point operations of a benchmark, if they are counted."""
    m = re.fullmatch(r"(gemvT?|ger|trsv lower|trsv upper) (\d+) ×(\d+)", name)
    if m:
        k, n, reps = m.group(1), int(m.group(2)), int(m.group(3))
        return (1 if k.startswith("trsv") else 2) * n * n * reps
    m = re.fullmatch(r"gemm(?:Naive)? (\d+)", name)
    if m:
        n = int(m.group(1))
        return 2 * n * n * n
    return None


def other_name(name):
    """The name of the benchmark of a C BLAS that `name` compares with."""
    return re.sub(r"^gemmNaive ", "gemm ", name)


def main():
    if len(sys.argv) < 3 or any("=" not in a for a in sys.argv[2:]):
        sys.exit(__doc__)
    order, lean = load(sys.argv[1])
    others = []
    for arg in sys.argv[2:]:
        label, _, path = arg.partition("=")
        others.append((label, load(path)[1]))
    cols = "".join(f" {label} | {label} / BLAS |" for label, _ in others)
    print(f"| Benchmark | Unit | BLAS |{cols}")
    print("|---|---|--:|" + "--:|--:|" * len(others))
    for name in order:
        other = other_name(name)
        if not any(other in t for _, t in others):
            continue
        f = flops(name)
        unit = "GFLOP/s" if f else "ms"

        def show(ms):
            return f"{f / (ms * 1e6):.2f}" if f else f"{ms:.3f}"

        row = f"| {name} | {unit} | {show(lean[name])} |"
        for _, t in others:
            if other in t:
                row += f" {show(t[other])} | {lean[name] / t[other]:.2f} |"
            else:
                row += " — | — |"
        print(row)


if __name__ == "__main__":
    main()
