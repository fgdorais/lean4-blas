/*
 * Copyright © 2026 François G. Dorais. All rights reserved.
 * Released under Apache 2.0 license as described in the file LICENSE.
 *
 * Times a C BLAS on the benchmarks of `lake exe bench`, for comparison. It is not part of the
 * library, which has no C dependency.
 *
 * It loads the CBLAS interface from a shared library at run time, so the same binary times any
 * implementation, for example OpenBLAS and Netlib's reference BLAS:
 *
 *   cc -O2 -o cblas_bench scripts/cblas_bench.c -ldl
 *   ./cblas_bench /usr/lib/x86_64-linux-gnu/blas/libblas.so.3 [size] [rounds]
 *
 * It prints `name<TAB>milliseconds` lines, with the names, inputs, repetitions and sizes of
 * `lake exe bench --tsv`, and each time is the fastest of `rounds` runs. `scripts/blas_compare.py`
 * puts the two side by side.
 */
#include <dlfcn.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* The CBLAS enums, with the values of the reference `cblas.h`. */
enum { RowMajor = 101, ColMajor = 102 };
enum { NoTrans = 111, Trans = 112 };
enum { Upper = 121, Lower = 122 };
enum { NonUnit = 131 };

static double (*ddot)(int, const double *, int, const double *, int);
static void (*daxpy)(int, double, const double *, int, double *, int);
static void (*dscal)(int, double, double *, int);
static void (*dcopy)(int, const double *, int, double *, int);
static double (*dasum)(int, const double *, int);
static double (*dnrm2)(int, const double *, int);
static size_t (*idamax)(int, const double *, int);
static void (*dgemv)(int, int, int, int, double, const double *, int, const double *, int,
                     double, double *, int);
static void (*dger)(int, int, int, double, const double *, int, const double *, int, double *,
                    int);
static void (*dtrsv)(int, int, int, int, int, const double *, int, double *, int);
static void (*dgemm)(int, int, int, int, int, int, double, const double *, int, const double *,
                     int, double, double *, int);

static void *sym(void *lib, const char *name) {
  void *p = dlsym(lib, name);
  if (!p) {
    fprintf(stderr, "missing %s\n", name);
    exit(1);
  }
  return p;
}

static int rounds = 10;
static const int reps = 10;
/* Keeps the results live. */
static volatile double sink;

static uint64_t now(void) {
  struct timespec t;
  clock_gettime(CLOCK_MONOTONIC, &t);
  return (uint64_t)t.tv_sec * 1000000000u + (uint64_t)t.tv_nsec;
}

/* Prints the fastest of `rounds` runs of `f`, in milliseconds. */
static void time_it(const char *name, double (*f)(void *), void *env) {
  uint64_t best = UINT64_MAX;
  for (int r = 0; r < rounds; r++) {
    uint64_t t0 = now();
    sink += f(env);
    uint64_t t1 = now();
    if (t1 - t0 < best) best = t1 - t0;
  }
  printf("%s\t%.3f\n", name, best / 1e6);
}

/* The inputs of `lake exe bench`. */
static double *vec(size_t n) {
  double *x = malloc(n * sizeof(double));
  for (size_t i = 0; i < n; i++) x[i] = (double)(i % 7) - 3;
  return x;
}

static double *mat(int m, int s) {
  double *a = malloc((size_t)m * m * sizeof(double));
  for (int j = 0; j < m; j++)
    for (int i = 0; i < m; i++) a[i + (size_t)m * j] = (double)((i * 7 + j * 13 + s) % 11) - 5;
  return a;
}

/* What a benchmark works on: `x` is read, `z` is a scratch copy, `inc` is the stride. */
typedef struct {
  int n, inc;
  double *x, *z;
} L1;

/* The updates copy their input first, as the first update of `lake exe bench` does. */
static double b_axpy(void *e) {
  L1 *v = e;
  dcopy(v->n, v->x, v->inc, v->z, v->inc);
  for (int k = 0; k < reps; k++) daxpy(v->n, 0.5, v->x, v->inc, v->z, v->inc);
  return v->z[0];
}
static double b_scal(void *e) {
  L1 *v = e;
  dcopy(v->n, v->x, 1, v->z, 1);
  for (int k = 0; k < reps; k++) dscal(v->n, 0.5, v->z, 1);
  return v->z[0];
}
static double b_copy(void *e) {
  L1 *v = e;
  for (int k = 0; k < reps; k++) dcopy(v->n, v->x, 1, v->z, 1);
  return v->z[0];
}
static double b_dot(void *e) {
  L1 *v = e;
  return ddot(v->n, v->x, v->inc, v->x, v->inc);
}
static double b_asum(void *e) {
  L1 *v = e;
  return dasum(v->n, v->x, 1);
}
static double b_nrm2(void *e) {
  L1 *v = e;
  return dnrm2(v->n, v->x, 1);
}
static double b_iamax(void *e) {
  L1 *v = e;
  return (double)idamax(v->n, v->x, 1);
}

typedef struct {
  int m, inc;
  double *a, *x, *y, *b;
} L2;

static double b_gemv(void *e) {
  L2 *v = e;
  int m = v->m;
  dcopy(m, v->x, v->inc, v->y, v->inc);
  for (int k = 0; k < reps; k++)
    dgemv(ColMajor, NoTrans, m, m, 1.5, v->a, m, v->x, v->inc, 0.5, v->y, v->inc);
  return v->y[0];
}
static double b_gemvT(void *e) {
  L2 *v = e;
  int m = v->m;
  dcopy(m, v->x, 1, v->y, 1);
  for (int k = 0; k < reps; k++)
    dgemv(ColMajor, Trans, m, m, 1.5, v->a, m, v->x, 1, 0.5, v->y, 1);
  return v->y[0];
}
static double b_ger(void *e) {
  L2 *v = e;
  int m = v->m;
  memcpy(v->b, v->a, (size_t)m * m * sizeof(double));
  for (int k = 0; k < reps; k++) dger(ColMajor, m, m, 1.5, v->x, 1, v->x, 1, v->b, m);
  return v->b[0];
}
static double trsv(L2 *v, int uplo) {
  int m = v->m;
  for (int i = 0; i < m; i++) v->y[i] = 1.5 * v->x[i];
  for (int k = 0; k < reps; k++) dtrsv(ColMajor, uplo, NoTrans, NonUnit, m, v->b, m, v->y, 1);
  return v->y[0];
}
static double b_trsvL(void *e) { return trsv(e, Lower); }
static double b_trsvU(void *e) { return trsv(e, Upper); }

typedef struct {
  int m;
  double *a, *b, *c, *z;
} L3;

/* `gemm` of `lake exe bench` returns a new matrix, so this one writes into a copy of `C`. */
static double b_gemm(void *e) {
  L3 *v = e;
  int m = v->m;
  memcpy(v->z, v->c, (size_t)m * m * sizeof(double));
  dgemm(ColMajor, NoTrans, NoTrans, m, m, m, 1.5, v->a, m, v->b, m, 0.5, v->z, m);
  return v->z[0];
}

int main(int argc, char **argv) {
  if (argc < 2) {
    fprintf(stderr, "usage: %s libblas.so [size] [rounds]\n", argv[0]);
    return 1;
  }
  void *lib = dlopen(argv[1], RTLD_NOW | RTLD_LOCAL);
  if (!lib) {
    fprintf(stderr, "%s\n", dlerror());
    return 1;
  }
  int n = argc > 2 ? atoi(argv[2]) : 1000000;
  if (argc > 3) rounds = atoi(argv[3]);
  ddot = sym(lib, "cblas_ddot");
  daxpy = sym(lib, "cblas_daxpy");
  dscal = sym(lib, "cblas_dscal");
  dcopy = sym(lib, "cblas_dcopy");
  dasum = sym(lib, "cblas_dasum");
  dnrm2 = sym(lib, "cblas_dnrm2");
  idamax = sym(lib, "cblas_idamax");
  dgemv = sym(lib, "cblas_dgemv");
  dger = sym(lib, "cblas_dger");
  dtrsv = sym(lib, "cblas_dtrsv");
  dgemm = sym(lib, "cblas_dgemm");

  char name[64];
  L1 v = {n, 1, vec(n), vec(n)};
  snprintf(name, sizeof name, "axpy ×%d", reps);
  time_it(name, b_axpy, &v);
  snprintf(name, sizeof name, "scal ×%d", reps);
  time_it(name, b_scal, &v);
  snprintf(name, sizeof name, "copy ×%d", reps);
  time_it(name, b_copy, &v);
  time_it("dot", b_dot, &v);
  time_it("asum", b_asum, &v);
  time_it("nrm2", b_nrm2, &v);
  time_it("iamax", b_iamax, &v);
  L1 up = {n, 1, malloc(n * sizeof(double)), v.z};
  for (int i = 0; i < n; i++) up.x[i] = i;
  time_it("iamax (increasing)", b_iamax, &up);
  L1 v2 = {n, 2, vec(2 * (size_t)n), vec(2 * (size_t)n)};
  snprintf(name, sizeof name, "axpy ×%d, stride 2 / stride 1", reps);
  time_it(name, b_axpy, &v2);
  time_it("dot, stride 2 / stride 1", b_dot, &v2);

  int l2[] = {256, 1024, 2048};
  for (int s = 0; s < 3; s++) {
    int m = l2[s];
    L2 w = {m, 1, mat(m, 1), vec(m), vec(2 * (size_t)m), mat(m, 1)};
    snprintf(name, sizeof name, "gemv %d ×%d", m, reps);
    time_it(name, b_gemv, &w);
    snprintf(name, sizeof name, "gemvT %d ×%d", m, reps);
    time_it(name, b_gemvT, &w);
    snprintf(name, sizeof name, "ger %d ×%d", m, reps);
    time_it(name, b_ger, &w);
    L2 w2 = w;
    w2.inc = 2;
    w2.x = vec(2 * (size_t)m);
    snprintf(name, sizeof name, "gemv %d ×%d, stride 2 / stride 1", m, reps);
    time_it(name, b_gemv, &w2);
    for (int j = 0; j < m; j++)
      for (int i = 0; i < m; i++)
        w.b[i + (size_t)m * j] = i == j ? m + 4 + i : (double)((i * 7 + j * 13) % 11) - 5;
    snprintf(name, sizeof name, "trsv lower %d ×%d", m, reps);
    time_it(name, b_trsvL, &w);
    snprintf(name, sizeof name, "trsv upper %d ×%d", m, reps);
    time_it(name, b_trsvU, &w);
  }

  int l3[] = {64, 256, 512, 1024};
  for (int s = 0; s < 4; s++) {
    int m = l3[s];
    L3 g = {m, mat(m, 1), mat(m, 2), mat(m, 3), mat(m, 3)};
    snprintf(name, sizeof name, "gemm %d", m);
    time_it(name, b_gemm, &g);
  }
  return 0;
}
