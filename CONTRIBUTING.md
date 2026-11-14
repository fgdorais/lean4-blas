# Contributing

Thanks for your interest in Lean 4 / BLAS. This file collects the conventions the library follows.
When in doubt, copy what the code nearby already does.

## Building and testing

```sh
lake build --wfail   # the library, the tests and the benchmarks, with warnings as errors
lake test            # the `#guard` tests in `BLASTest`
lake exe bench       # the benchmarks, when a change may affect speed
```

CI runs `lake build --wfail`, `lake test` and `python3 scripts/generate.py --check` on Linux (x86
and ARM), macOS and Windows for every pull request to `main`. Add the `benchmark` label to a pull
request to compare its speed with its base.

## Generated files

The `Float32` routines, tests and benchmarks are generated from the `Float64` versions. Edit only
the templates, `BLAS/Float64.lean`, `BLAS/Float64/`, `BLASTest/Float64.lean`, `BLASTest/Float64/`
and `BLASBench/Float64.lean`, then regenerate the `Float32` files:

```sh
python3 scripts/generate.py           # regenerate
python3 scripts/generate.py --check   # check that nothing is out of date
```

Text that depends on the precision, such as the constants of `nrm2` and test tolerances, goes in
the `SPECIFIC` table of the script, which fails if such text is left over. `Float` becomes
`Float32`, two columns longer, so keep template lines that mention `Float` short enough for the
generated line to fit. Anything that doesn't name an element type, such as the `USize` index
lemmas, goes in `BLAS/Internal.lean` instead.

## Files

- Every Lean, Python and C file starts with the copyright and license header (workflows,
  lakefiles and `.git*` files don't), and every Lean file is a `module`.
- Each library module has a `/-! # Title -/` docstring, with `/-! ## … -/` headers for its parts.
- Every public declaration has a docstring (`linter.missingDocs` is on). Use `--` comments to
  explain why the code is the way it is.
- Mark declarations `public` one at a time, and `@[expose]` only where other modules must unfold
  the body. `BLAS.Internal` holds private lemmas that are not part of the API; the modules that
  need them use `import all BLAS.Internal`.
- Keep lines to 100 columns, except for Markdown tables and URLs.

## Lean style

- `variable` only right after `namespace` or a named `section`.
- `fun x => …`, not `↦` or `λ`; `<|` and `|>`, not `$`.
- `theorem`, not `lemma`.
- In attribute lists, `simp` comes before `grind`, and `expose` comes last: `@[simp, grind =]`,
  `@[inline, expose]`.
- Name unused hypotheses with a leading underscore (`_h`).
- Don't prefix a lemma with the name of a foreign type inside the library's namespaces.

## Proofs

- Use `lia` and `grind`, not `omega`.
- `lia` and `grind` run out of memory on literal `2^64` moduli, so keep `USize.size` symbolic.
- A `grind` or `lia` proof inside the body of an `inplace` loop captures the loop's state and stops
  the loop lemmas from matching. Use a named lemma there, such as `BLAS.toNat_succ_add`.
- Lemma names follow core and scalar-arrays: `getElem_axpy`, `data_axpy`, `size_gemmCol`.

## Design

- Specifications are exact `Float` equalities, in the order of operations of the reference BLAS
  (Reference-LAPACK `master`), with its special cases. A faster kernel must keep that order and be
  proved equal to the specification; a change that would reorder the operations, such as partial
  sums in `dot`, is not taken.
- Kernels are written with scalar-arrays' `inplace … do` notation, whose loops carry at most four
  variables. Nested `inplace` loops more than two deep recurse on the stack, so split them into
  separate functions.
- Kernels fall back to the specification when the array is too large for `USize` indices, so that
  the specifications need no size hypotheses.
- The library has no dependencies besides lean4-scalar-arrays, pinned to an exact release, and no
  C code of its own. `scripts/cblas_bench.c` is only a benchmark.

## Naming

- Routines keep the names of the reference BLAS without the precision prefix: `axpy`, `gemv`,
  `trsm`. Variants with a transposed or right-hand argument add a suffix: `gemvT`, `trsmRight`.
- `foo?` returns an `Option`, and `foo!` may panic on bad input: `iamax?` is `none` for the empty
  vector and `iamax!` is `0`, while `iamax` takes a proof that the vector is nonempty.

## Commits and pull requests

- Pull requests are squash-merged. The title is the commit message, in the
  [Conventional Commits](https://www.conventionalcommits.org) style, in lower case:
  `feat: …`, `fix: …`, `perf: …`, `refactor: …`, `docs: …` or `chore: …`. Changes to CI and
  workflows are `chore:`.
- Don't rewrite a branch's history after pushing it; merge `main` into it instead.
- Releases are git tags `vX.Y.Z`; the lakefile has no version.
