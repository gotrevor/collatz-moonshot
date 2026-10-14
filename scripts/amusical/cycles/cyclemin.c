/*
 * cyclemin.c -- certify that no integer n in [lo, hi) is the minimum of a positive
 * U-cycle of period P with 1 <= P <= 2H, except the cycles it reports.
 *
 * U(2n)=3n, U(4n+1)=3n+1, U(4n+3)=3n+2;  V = U^{-1}: V(3m)=2m, V(3m+1)=4m+1, V(3m+2)=4m+3.
 *
 * Lemma (cycle-minimum test).  Let n >= 1 be the minimum of a cycle of period P <= 2H.
 *   (i)  U^j n > n and V^j n > n for all 1 <= j < P   (minimum, elements distinct);
 *   (ii) U^P n = n;  and if P > H then U^{P-H} n = V^H n with 1 <= P-H <= H.
 * Algorithm per n: run U and V in lockstep for j = 1..H.
 *   - value < n          -> n is not the minimum of any cycle of period <= 2H    ("dip")
 *   - value == n         -> n is periodic with period j: REPORT
 *   - survived both      -> t = V^H n; n is periodic with period a+H iff U^a n == t
 *                           for some 1 <= a <= H.  Forward values are kept as
 *                           (limb-count, low limb) fingerprints; a fingerprint match is
 *                           re-verified exactly by recomputation.
 * (A dip at j before any return rules out every period P: P <= j would have returned
 *  first; P > j contradicts minimality.)
 *
 * Output: one line per periodic n found: "CYCLE n period".  Summary to stderr.
 * Usage: cyclemin lo hi H [skipknown=1] [q=1]
 * For q > 1 (the layer U_q of the research note), candidates are n > q/3; every value
 * visited before a dip is >= n > q/3, which keeps U_q and V_q positive.
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MAXL 400        /* limbs: 400*64 = 25600 bits >= 0.585*H + 64 for H <= 43000 */
typedef unsigned __int128 u128;

typedef struct { int n; uint64_t d[MAXL]; } big;

static void set_u64(big *x, uint64_t v) { x->n = 1; x->d[0] = v; }

static uint64_t Q = 1;   /* layer: U_q(2n)=3n, U_q(r)=(3r+q)/4 if r=q (4), (3r-q)/4 if r=3q (4) */

static void add_small(big *x, uint64_t v) {
    int i = 0;
    uint64_t s = x->d[0] + v;
    int c = s < v;
    x->d[0] = s;
    while (c) { i++; if (i == x->n) { x->d[i] = 1; x->n++; break; } x->d[i]++; c = (x->d[i] == 0); }
}
static void sub_small(big *x, uint64_t v) {   /* requires x >= v */
    uint64_t s = x->d[0];
    x->d[0] = s - v;
    if (s < v) { int i = 1; while (x->d[i] == 0) { x->d[i] = ~0ULL; i++; } x->d[i]--; }
    while (x->n > 1 && x->d[x->n - 1] == 0) x->n--;
}

/* x <- U_q(x); requires x > q/3 so the result is positive */
static void stepU(big *x) {
    uint64_t r = x->d[0] & 3;
    int s = (r & 1) ? 2 : 1;
    uint64_t carry = 0;
    int n = x->n;
    for (int i = 0; i < n; i++) {
        u128 t = (u128)x->d[i] * 3 + carry;
        x->d[i] = (uint64_t)t;
        carry = (uint64_t)(t >> 64);
    }
    if (carry) { x->d[n] = carry; n++; }
    x->n = n;
    if (r & 1) {
        if (r == (Q & 3)) add_small(x, Q); else sub_small(x, Q);
        n = x->n;
    }
    for (int i = 0; i < n - 1; i++)
        x->d[i] = (x->d[i] >> s) | (x->d[i + 1] << (64 - s));
    x->d[n - 1] >>= s;
    while (n > 1 && x->d[n - 1] == 0) n--;
    x->n = n;
    if (n >= MAXL - 2) { fprintf(stderr, "overflow\n"); exit(3); }
}

static unsigned mod3(const big *x) {
    u128 acc = 0;                   /* 2^64 = 1 mod 3 */
    for (int i = 0; i < x->n; i++) acc += x->d[i];
    return (unsigned)(acc % 3);
}

#define INV3 0xAAAAAAAAAAAAAAABULL  /* 3^{-1} mod 2^64 */

/* x <- V_q(x):  x=0 (3): 2x/3 ; x=q (3): (4x-q)/3 ; x=-q (3): (4x+q)/3 */
static void stepV(big *x) {
    unsigned r = mod3(x);
    int sh = (r == 0) ? 1 : 2;
    int n = x->n;
    uint64_t top = x->d[n - 1] >> (64 - sh);
    for (int i = n - 1; i > 0; i--)
        x->d[i] = (x->d[i] << sh) | (x->d[i - 1] >> (64 - sh));
    x->d[0] <<= sh;
    if (top) { x->d[n] = top; n++; }
    x->n = n;
    if (r != 0) {
        if (r == Q % 3) sub_small(x, Q); else add_small(x, Q);
        n = x->n;
    }
    uint64_t c = 0;
    for (int i = 0; i < n; i++) {
        uint64_t s = x->d[i];
        uint64_t l = s - c;
        c = (l > s);
        uint64_t q = l * INV3;
        x->d[i] = q;
        c += (uint64_t)(((u128)q * 3) >> 64);
    }
    if (c) { fprintf(stderr, "divexact error\n"); exit(4); }
    while (n > 1 && x->d[n - 1] == 0) n--;
    x->n = n;
    if (n >= MAXL - 2) { fprintf(stderr, "overflow\n"); exit(3); }
}

/* compare big with small v: -1,0,1 */
static int cmp_small(const big *x, uint64_t v) {
    if (x->n > 1) return 1;
    return (x->d[0] < v) ? -1 : (x->d[0] > v);
}

static int big_eq(const big *a, const big *b) {
    return a->n == b->n && memcmp(a->d, b->d, sizeof(uint64_t) * a->n) == 0;
}

int main(int argc, char **argv) {
    if (argc < 4) { fprintf(stderr, "usage: cyclemin lo hi H [skipknown=1]\n"); return 1; }
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int H = atoi(argv[3]);
    int skipknown = argc > 4 ? atoi(argv[4]) : 1;
    if (argc > 5) Q = strtoull(argv[5], 0, 10);
    if (Q % 2 == 0 || Q % 3 == 0) { fprintf(stderr, "q must be prime to 6\n"); return 1; }
    if (lo <= Q / 3) lo = Q / 3 + 1;   /* candidates n > q/3 keep all visited values positive */
    static big f, g, t;
    uint64_t *fp_low = malloc(sizeof(uint64_t) * (H + 1));
    int *fp_n = malloc(sizeof(int) * (H + 1));
    uint64_t ndip = 0, nsurv = 0, nfound = 0, ncoll = 0;
    long double steps = 0;
    int maxlimbs = 1;
    for (uint64_t n = (lo < 1 ? 1 : lo); n < hi; n++) {
        if (skipknown && Q == 1 && (n == 1 || n == 2 || n == 4 || n == 44)) continue;
        set_u64(&f, n); set_u64(&g, n);
        int done = 0, j;
        for (j = 1; j <= H; j++) {
            stepU(&f);
            int c = cmp_small(&f, n);
            if (c < 0) { ndip++; done = 1; break; }
            if (c == 0) { printf("CYCLE %llu %d\n", (unsigned long long)n, j); nfound++; done = 1; break; }
            fp_low[j] = f.d[0]; fp_n[j] = f.n;
            stepV(&g);
            c = cmp_small(&g, n);
            if (c < 0) { ndip++; done = 1; break; }
            if (c == 0) { printf("CYCLE %llu %d\n", (unsigned long long)n, j); nfound++; done = 1; break; }
        }
        steps += 2.0L * (j > H ? H : j);
        if (f.n > maxlimbs) maxlimbs = f.n;
        if (g.n > maxlimbs) maxlimbs = g.n;
        if (done) continue;
        nsurv++;
        /* meet test: U^a n == V^H n for some 1 <= a <= H ? */
        for (int a = 1; a <= H; a++) {
            if (fp_n[a] == g.n && fp_low[a] == g.d[0]) {
                ncoll++;
                set_u64(&t, n);
                for (int b = 0; b < a; b++) stepU(&t);
                if (big_eq(&t, &g)) {
                    printf("CYCLE %llu %d\n", (unsigned long long)n, a + H);
                    nfound++;
                    break;
                }
            }
        }
    }
    fprintf(stderr, "range [%llu,%llu) H=%d: dips=%llu survivors=%llu found=%llu fpcoll=%llu steps=%.4Le maxlimbs=%d\n",
            (unsigned long long)lo, (unsigned long long)hi, H,
            (unsigned long long)ndip, (unsigned long long)nsurv, (unsigned long long)nfound,
            (unsigned long long)ncoll, steps, maxlimbs);
    return 0;
}
