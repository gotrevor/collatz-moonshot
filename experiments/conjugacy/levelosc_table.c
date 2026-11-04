/* Probe for the node SliceOscDecay (BeyondWordsLinear.lean); compiled twin of levelosc_table.js.
 * Exact over all 2^j starts:
 *   levelOsc j a m / #levelSet j a = sum_{y<3^a} |mu(y) - 3^{m-a} mu(y mod 3^m)| / card,
 * for the central slices a = j/2 - 1, j/2, j/2 + 1 and the sparse-edge slice a = floor(3j/5),
 * all 1 <= m <= a (m = a is 0 by definition and printed as such).
 *
 * The box has no libc headers or system C compiler; build with Lean's bundled toolchain:
 *   leanc -O2 levelosc_table.c -o levelosc_table
 * Usage: ./levelosc_table THREADS j1 j2 ...    (add 'noedge' as the last argument to skip
 * the edge slice, whose 3^a mass array dominates memory).
 * Output lines match levelosc_table.js: j a n card/3^a ratio(m=1) ... ratio(m=a).
 */
#include <stdint.h>
#include <stddef.h>
int printf(const char *, ...);
int fflush(void *);
void *calloc(size_t, size_t);
void free(void *);
long atol(const char *);
int strcmp(const char *, const char *);
typedef unsigned long pthread_t;
int pthread_create(pthread_t *, const void *, void *(*)(void *), void *);
int pthread_join(pthread_t, void **);

#define MAXS 4
#ifndef PREC
#define PREC " %.3f"
#endif
static int J, NS, NT;
static int sl[MAXS];
static uint16_t *mass[MAXS];
static uint64_t pw3[40];
static volatile int overflow = 0;

typedef struct { int id; uint64_t lo, hi; } job_t;

static void *enum_worker(void *arg) {
  job_t *jb = (job_t *)arg;
  for (uint64_t r = jb->lo; r < jb->hi; r++) {
    uint64_t x = r; int a = 0;
    for (int i = 0; i < J; i++) {
      uint64_t b = x & 1;
      x = (x + b * (2 * x + 1)) >> 1;
      a += (int)b;
    }
    for (int s = 0; s < NS; s++)
      if (a == sl[s]) {
        if (x >= pw3[a]) { overflow = 2; break; }
        uint16_t old = __atomic_fetch_add(&mass[s][x], 1, __ATOMIC_RELAXED);
        if (old == 65535) overflow = 1;
        break;
      }
  }
  return 0;
}

/* per (slice, m): cls_m[c] = sum_{d<3} cls_{m+1}[c + d 3^m] (cls_a = mu), and
 * tot = sum_y |mu(y) - q cls_m[y mod M]|, scanned sequentially in y. */
static uint16_t *cur_mu; static uint64_t *cur_cls, *nxt_cls; static uint64_t cur_N, cur_M;
static double cur_q; static double part[64];

static void *down_worker(void *arg) {
  job_t *jb = (job_t *)arg;
  for (uint64_t c = jb->lo; c < jb->hi; c++)
    nxt_cls[c] = cur_cls[c] + cur_cls[c + cur_M] + cur_cls[c + 2 * cur_M];
  return 0;
}

static void *top_worker(void *arg) {
  job_t *jb = (job_t *)arg;
  for (uint64_t c = jb->lo; c < jb->hi; c++)
    nxt_cls[c] = (uint64_t)cur_mu[c] + cur_mu[c + cur_M] + cur_mu[c + 2 * cur_M];
  return 0;
}

static void *tot_worker(void *arg) {
  job_t *jb = (job_t *)arg;
  double t = 0;
  uint64_t c = jb->lo % cur_M;
  for (uint64_t y = jb->lo; y < jb->hi; y++) {
    double d = (double)cur_mu[y] - cur_q * (double)cur_cls[c];
    t += d < 0 ? -d : d;
    if (++c == cur_M) c = 0;
  }
  part[jb->id] = t;
  return 0;
}

static void run_par(void *(*f)(void *), uint64_t total) {
  pthread_t th[64]; job_t jb[64];
  for (int t = 0; t < NT; t++) {
    jb[t].id = t; jb[t].lo = total * t / NT; jb[t].hi = total * (t + 1) / NT;
    pthread_create(&th[t], 0, f, &jb[t]);
  }
  for (int t = 0; t < NT; t++) pthread_join(th[t], 0);
}

int main(int argc, char **argv) {
  pw3[0] = 1; for (int i = 1; i < 40; i++) pw3[i] = 3 * pw3[i - 1];
  NT = (int)atol(argv[1]); if (NT > 64) NT = 64;
  int last = argc, edge = 1;
  if (strcmp(argv[argc - 1], "noedge") == 0) { edge = 0; last = argc - 1; }
  for (int k = 2; k < last; k++) {
    J = (int)atol(argv[k]);
    NS = 0;
    for (int a = J / 2 - 1; a <= J / 2 + 1; a++) sl[NS++] = a;
    if (edge && (3 * J) / 5 > J / 2 + 1) sl[NS++] = (3 * J) / 5;
    for (int s = 0; s < NS; s++) mass[s] = calloc(pw3[sl[s]], sizeof(uint16_t));
    overflow = 0;
    run_par(enum_worker, (uint64_t)1 << J);
    if (overflow) { printf("j=%d OVERFLOW %d\n", J, overflow); return 1; }
    for (int s = 0; s < NS; s++) {
      int a = sl[s];
      uint64_t N = pw3[a], cnt = 0;
      for (uint64_t y = 0; y < N; y++) cnt += mass[s][y];
      printf("j=%d a=%d n=%lu card/3^a=%.2f", J, a, (unsigned long)cnt, (double)cnt / (double)N);
      cur_mu = mass[s]; cur_N = N;
      double res[40];
      uint64_t *prev = 0;
      for (int m = a - 1; m >= 1; m--) {
        cur_M = pw3[m];
        nxt_cls = calloc(cur_M, sizeof(uint64_t));
        if (prev == 0) run_par(top_worker, cur_M);
        else { cur_cls = prev; run_par(down_worker, cur_M); free(prev); }
        prev = nxt_cls; cur_cls = prev; cur_q = 1.0 / (double)pw3[a - m];
        run_par(tot_worker, N);
        double tot = 0; for (int t = 0; t < NT; t++) tot += part[t];
        res[m] = tot / (double)cnt;
      }
      free(prev);
      for (int m = 1; m < a; m++) printf(PREC, res[m]);
      printf(" 0.000\n"); fflush(0);
      free(mass[s]);
    }
  }
  return 0;
}
