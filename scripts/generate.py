#!/usr/bin/env python3
# Copyright © 2026 François G. Dorais. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
"""
Generates the `Float32` routines and their tests from the `Float64` versions.

`BLAS/Float64.lean`, `BLAS/Float64/`, `BLASTest/Float64.lean` and `BLASTest/Float64/` are the
templates: make changes there, then run this script from anywhere to regenerate the `Float32`
files, the root import lists and `.gitattributes`, which marks the generated files so that GitHub
collapses them in diffs.

Most of the translation is mechanical: `Float64` becomes `Float32`, `Float` becomes `Float32` and
`Nat.toFloat` becomes `Nat.toFloat32`. Text that depends on the precision, such as the constants of
Blue's algorithm in `nrm2`, test values beyond the range of `Float32` and test tolerances, is
translated by the table `SPECIFIC`. The script fails if precision-dependent text is left over: a
`Float.ofBits` constant, or a literal whose exponent is beyond the range of `Float32`.

With `--check`, it changes nothing and exits with status 1 if any generated file is out of date.
With `--verbose`, it lists the entries of `SPECIFIC` that are not in the templates.
"""

import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent

# The directories and modules that are templates, relative to the repository root.
LIBS = ['BLAS', 'BLASTest']

# Precision-dependent text: each entry is the `Float64` text and its `Float32` translation, which
# replaces it before the mechanical translation. An entry need not occur in the templates: the
# script then only warns, so that the table can be ready before the templates use it.
#
# Blue's constants (`dnrm2.f90` and `snrm2.f90` in the reference BLAS), for a binary format with
# `digits` bits of precision and exponents from `minexponent` to `maxexponent` (Fortran's
# conventions):
#   tsml = 2 ^ ceiling((minexponent - 1) / 2)       Float64: 2 ^ (-511)   Float32: 2 ^ (-63)
#   tbig = 2 ^ floor((maxexponent - digits + 1) / 2) Float64: 2 ^ 486     Float32: 2 ^ 52
#   ssml = 2 ^ (-floor((minexponent - digits) / 2)) Float64: 2 ^ 537      Float32: 2 ^ 75
#   sbig = 2 ^ (-ceiling((maxexponent + digits - 1) / 2)) Float64: 2 ^ (-538) Float32: 2 ^ (-76)
SPECIFIC = [
  # Blue's constants in `nrm2`.
  ('`2 ^ (-511)`', '`2 ^ (-63)`'),
  ('Float.ofBits 0x2000000000000000', 'Float32.ofBits 0x20000000'),
  ('`2 ^ 486`', '`2 ^ 52`'),
  ('Float.ofBits 0x5E50000000000000', 'Float32.ofBits 0x59800000'),
  ('`2 ^ 537`', '`2 ^ 75`'),
  ('Float.ofBits 0x6180000000000000', 'Float32.ofBits 0x65000000'),
  ('`2 ^ (-538)`', '`2 ^ (-76)`'),
  ('Float.ofBits 0x1E50000000000000', 'Float32.ofBits 0x19800000'),
  ('Float.ofBits 0x7FEFFFFFFFFFFFFF', 'Float32.ofBits 0x7F7FFFFF'),
  ('`dnrm2.f90`', '`snrm2.f90`'),
  # The tests of `nrm2` with elements whose squares overflow or underflow.
  ('Float.scaleB 3 600, Float.scaleB (-4) 600]) == Float.scaleB 5 600',
   'Float.scaleB 3 80, Float.scaleB (-4) 80]) == Float.scaleB 5 80'),
  ('Float.scaleB 3 (-600), Float.scaleB 4 (-600)', 'Float.scaleB 3 (-80), Float.scaleB 4 (-80)'),
  ('Float.scaleB 5 (-600)', 'Float.scaleB 5 (-80)'),
  ('Float.scaleB 3 1020, Float.scaleB 4 1020', 'Float.scaleB 3 124, Float.scaleB 4 124'),
  ('Float.scaleB 5 1020', 'Float.scaleB 5 124'),
  ('Float.scaleB 3 (-1060), Float.scaleB 4 (-1060)',
   'Float.scaleB 3 (-140), Float.scaleB 4 (-140)'),
  ('Float.scaleB 5 (-1060)', 'Float.scaleB 5 (-140)'),
  ('[1e-300, 1]', '[1e-30, 1]'),
  ('[1e300, 1e300]', '[1e30, 1e30]'),
  ('[1e-300, 0 / 0]', '[1e-30, 0 / 0]'),
  # The test of `trsv` against the reference loops: the unit solves of size 300 overflow `Float32`
  # (to `NaN`, which is not equal to itself); those of size 80 don't.
  ('trsvMatches 300 u d', 'trsvMatches 80 u d'),
  # The tolerance of the residual of `trsv`.
  ('< 1e-12', '< 1e-4'),
  # The rotations: the reference routines, and the constants of `srotg.f90` and `srotmg.f`.
  ('`drot`', '`srot`'),
  ('`drotm`', '`srotm`'),
  ('`drotg`', '`srotg`'),
  ('`drotmg`', '`srotmg`'),
  ('`2⁻¹⁰²²`', '`2⁻¹²⁶`'),
  ('Float.ofBits 0x0010000000000000', 'Float32.ofBits 0x00800000'),
  ('`2¹⁰²³`', '`2¹²⁷`'),
  ('Float.ofBits 0x7FE0000000000000', 'Float32.ofBits 0x7F000000'),
  ("the literal `16777216.D0`, which is `gam * gam`", "the literal `1.67772E7`, a little less than `gam * gam`"),
  ('public def gamsq : Float := 16777216', 'public def gamsq : Float := 1.67772e7'),
  ('the literal `5.9604645D-8`', 'the literal `5.96046E-8`'),
  ('public def rgamsq : Float := 5.9604645e-8', 'public def rgamsq : Float := 5.96046e-8'),
  # The tests of `rotg` whose squares overflow or underflow.
  ('Float.scaleB 3 1000) (Float.scaleB 4 1000)).r == Float.scaleB 5 1000',
   'Float.scaleB 3 120) (Float.scaleB 4 120)).r == Float.scaleB 5 120'),
  ('Float.scaleB 3 (-1000)) (Float.scaleB 4 (-1000))).r == Float.scaleB 5 (-1000)',
   'Float.scaleB 3 (-120)) (Float.scaleB 4 (-120))).r == Float.scaleB 5 (-120)'),
]

# The mechanical translation, after `SPECIFIC`: regular expressions and their replacements.
MECHANICAL = [
  (r'Float64', 'Float32'),
  (r'\bFloat\b', 'Float32'),
  (r'\.toFloat\b', '.toFloat32'),
]

# Precision-dependent text that `SPECIFIC` should have translated.
LEFTOVER = [
  (r'Float32\.ofBits 0x[0-9A-Fa-f]{9,}', 'a 64-bit `Float.ofBits` constant'),
  (r'\b\d+(\.\d+)?[eE][+-]?(39|[4-9]\d|\d{3,})\b', 'a literal beyond the range of `Float32`'),
  (r'\bscaleB\s+\S+\s+\(?-?(1[5-9]\d|[2-9]\d\d|\d{4,})\)?', 'an exponent beyond `Float32`'),
]


def templates():
    """Maps the paths of the templates, relative to the repository root, to their contents."""
    files = {}
    for lib in LIBS:
        files[f'{lib}/Float64.lean'] = None
        for p in sorted((ROOT / lib / 'Float64').rglob('*.lean')):
            files[str(p.relative_to(ROOT))] = None
    return {p: (ROOT / p).read_text() for p in files if (ROOT / p).exists()}


def translate(path, s, used):
    for a, b in SPECIFIC:
        if a in s:
            used.add(a)
            s = s.replace(a, b)
    for a, b in MECHANICAL:
        s = re.sub(a, b, s)
    for pattern, what in LEFTOVER:
        m = re.search(pattern, s)
        if m:
            line = s.count('\n', 0, m.start()) + 1
            sys.exit(f'{path}:{line}: {what} is left over, {m.group(0)!r}: add it to `SPECIFIC`')
    return s


def root_imports(path):
    """The root module `path`, with its imports of `{lib}.Float64` followed by `Float32`."""
    s = (ROOT / path).read_text()
    lib = path.removesuffix('.lean')
    old = f'import {lib}.Float64\n'
    assert old in s, f'{path}: no import of {lib}.Float64'
    s = re.sub(rf'^((?:public )?import {lib}\.Float32\n)', '', s, flags=re.M)
    return re.sub(rf'^((?:public )?)import {lib}\.Float64\n',
                  lambda m: f'{m.group(1)}import {lib}.Float64\n{m.group(1)}import {lib}.Float32\n',
                  s, flags=re.M)


def generate():
    """Returns a map from paths relative to the repository root to their generated contents."""
    used = set()
    files = {}
    for path, s in templates().items():
        files[path.replace('Float64', 'Float32')] = translate(path, s, used)
    unused = [a for a, _ in SPECIFIC if a not in used]
    if unused and '--verbose' in sys.argv:
        print('Not in the templates:', *map(repr, unused), sep='\n  ', file=sys.stderr)
    for lib in LIBS:
        files[f'{lib}.lean'] = root_imports(f'{lib}.lean')
    files['.gitattributes'] = (
        '# Files generated by `scripts/generate.py` from the `Float64` templates. GitHub collapses\n'
        '# them in diffs.\n'
        + ''.join(f'{lib}/Float32.lean linguist-generated\n{lib}/Float32/** linguist-generated\n'
                  for lib in LIBS))
    return files


def main():
    check = '--check' in sys.argv[1:]
    files = generate()
    stale = []
    for path, contents in files.items():
        file = ROOT / path
        if not file.exists() or file.read_text() != contents:
            stale.append(path)
            if not check:
                file.parent.mkdir(parents=True, exist_ok=True)
                file.write_text(contents)
    # Generated files whose template is gone.
    for lib in LIBS:
        for p in sorted((ROOT / lib / 'Float32').rglob('*.lean')):
            path = str(p.relative_to(ROOT))
            if path not in files:
                stale.append(path)
                if not check:
                    p.unlink()
    if check and stale:
        print('Out of date; run scripts/generate.py:', *stale, sep='\n  ')
        sys.exit(1)


if __name__ == '__main__':
    main()
