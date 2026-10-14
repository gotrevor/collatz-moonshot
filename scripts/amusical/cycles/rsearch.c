/*
 * rsearch.c -- certify that no n in [lo, hi) is the minimum of a positive U-cycle with at most
 * R maximal E-runs (R local minima), except the cycles it reports.
 *
 * If n is the minimum of a cycle with r <= R E-runs then (i) n is even (else U(n) < n) unless
 * n = 1; n starts an E-run; (ii) all forward and backward iterates before return exceed n;
 * (iii) walking forward from n the cycle returns to n before an (r+1)-th E-run starts.
 * Per n: lockstep forward U and backward V; stop on a value < n (dip), a forward return to n
 * (REPORT), or the start of an (R+1)-th forward E-run.  Arithmetic: unsigned __int128 with a
 * guard at 2^124; a guarded n is printed as OVERFLOW and must be settled separately.
 * Usage: rsearch lo hi R [skipknown=1]
 */
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
typedef unsigned __int128 u128;
static const u128 GUARD = ((u128)1) << 124;

static inline u128 U(u128 x) {
    if (!(x & 1)) return (x >> 1) * 3;
    if ((x & 3) == 1) return (3 * x + 1) >> 2;
    return (3 * x - 1) >> 2;
}
static const u128 INV3_128 = (((u128)0xAAAAAAAAAAAAAAAAULL) << 64) | 0xAAAAAAAAAAAAAAABULL; /* 3^-1 mod 2^128 */
static inline unsigned mod3_128(u128 x) {   /* 2^64 = 1 (mod 3) */
    uint64_t a = (uint64_t)x, b = (uint64_t)(x >> 64);
    return (unsigned)((a % 3 + b % 3) % 3);
}
/* exact division by 3 via the inverse mod 2^128 (valid: numerator divisible by 3, < 2^128) */
static inline u128 V(u128 x) {
    unsigned r = mod3_128(x);
    if (r == 0) return (x * INV3_128) * 2;
    if (r == 1) return (4 * x - 1) * INV3_128;
    return (4 * x + 1) * INV3_128;
}

int main(int argc, char **argv) {
    uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
    int R = atoi(argv[3]);
    int skipknown = argc > 4 ? atoi(argv[4]) : 1;
    uint64_t ndip = 0, nruns = 0, nfound = 0, nover = 0;
    double steps = 0;
    for (uint64_t n = (lo < 1 ? 1 : lo); n < hi; n++) {
        if (skipknown && (n == 1 || n == 2 || n == 4 || n == 44)) continue;
        u128 f = n, g = n;
        int runs = 1;             /* run 1 starts at n (if n even) */
        int prev_odd = 0;
        long j = 0;
        for (;;) {
            j++;
            int fodd = (int)(f & 1);
            f = U(f);
            if (f == n) { printf("CYCLE %llu %ld\n", (unsigned long long)n, j); nfound++; break; }
            if (f < n) { ndip++; break; }
            prev_odd = fodd;
            if (!(f & 1) && prev_odd) {      /* a new E-run starts at f */
                runs++;
                if (runs > R) { nruns++; break; }
            }
            g = V(g);
            if (g < n) { ndip++; break; }
            if (g == n) { printf("CYCLE %llu %ld (backward)\n", (unsigned long long)n, j); nfound++; break; }
            if (f >= GUARD || g >= GUARD) { printf("OVERFLOW %llu\n", (unsigned long long)n); nover++; break; }
        }
        steps += 2.0 * j;
    }
    fprintf(stderr, "range [%llu,%llu) R=%d: dips=%llu runcap=%llu found=%llu overflow=%llu steps=%.4e\n",
            (unsigned long long)lo, (unsigned long long)hi, R, (unsigned long long)ndip,
            (unsigned long long)nruns, (unsigned long long)nfound, (unsigned long long)nover, steps);
    return 0;
}
