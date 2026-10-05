/* Orbit hunt over Nashida's open entangled G_2 benchmark, far past his x <= 500 test.
 *
 * Reads "k<TAB>spec<TAB>category" lines (maps_G2_open.tsv) on stdin; for each map runs every start
 * 1 <= x <= N for at most S steps, with exact 128-bit arithmetic, and reports per map:
 *   CYCLE  min period          a positive periodic orbit (the map does NOT terminate)
 *   ESCAPE start steps         an orbit exceeded 2^120 (numerical evidence of divergence only)
 *   CAP    start               an orbit neither halted, cycled nor escaped within S steps
 * Maps with none of these print nothing.  Halting follows Nashida's GMap.step: a halting residue,
 * or an image < 1.
 *
 *   cc -O2 -o /tmp/g2_orbit_hunt g2_orbit_hunt.c
 *   tail -n +2 maps_G2_open.tsv | g2_orbit_hunt N S
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef __int128 i128;
static int A[4], B[4], E[4], live[4];

#define HBITS 20
#define HSIZE (1u << HBITS)
static i128 hval[HSIZE];
static unsigned hstamp[HSIZE];
static unsigned stamp;

static int hinsert(i128 v) { /* 1 if already present this stamp */
    unsigned long long h = (unsigned long long)(v ^ (v >> 64)) * 0x9E3779B97F4A7C15ull;
    unsigned i = (unsigned)(h >> (64 - HBITS));
    for (;;) {
        if (hstamp[i] != stamp) { hstamp[i] = stamp; hval[i] = v; return 0; }
        if (hval[i] == v) return 1;
        i = (i + 1) & (HSIZE - 1);
    }
}

static int step(i128 x, i128 *y) {
    int r = (int)(x & 3);
    if (!live[r]) return 0;
    i128 t = (i128)A[r] * x + B[r];
    t >>= E[r]; /* exact: 2^e | A r + b */
    if (t < 1) return 0;
    *y = t;
    return 1;
}

static void print128(i128 v) {
    char buf[64]; int n = 0;
    if (v == 0) { putchar('0'); return; }
    while (v > 0) { buf[n++] = '0' + (int)(v % 10); v /= 10; }
    while (n) putchar(buf[--n]);
}

int main(int argc, char **argv) {
    long N = argc > 1 ? atol(argv[1]) : 100000;
    long S = argc > 2 ? atol(argv[2]) : 100000;
    unsigned char *halts = calloc(N + 1, 1);
    i128 LIM = (i128)1 << 120;
    char line[512];
    while (fgets(line, sizeof line, stdin)) {
        char *spec = strchr(line, '\t');
        if (!spec) continue;
        spec++;
        char *tab = strchr(spec, '\t');
        if (tab) *tab = 0;
        char *nl = strchr(spec, '\n');
        if (nl) *nl = 0;
        char specbuf[512];
        strcpy(specbuf, spec);
        memset(live, 0, sizeof live);
        for (char *p = strtok(spec, ";"); p; p = strtok(NULL, ";")) {
            int r, a, b, e;
            if (sscanf(p, "%d:%d,%d,%d", &r, &a, &b, &e) == 4) { live[r] = 1; A[r] = a; B[r] = b; E[r] = e; }
        }
        memset(halts, 0, N + 1);
        i128 cyc_min = 0; int cyc_per = 0, ncyc = 0;
        long esc_start = 0, esc_steps = 0, cap_start = 0;
        for (long x0 = 1; x0 <= N; x0++) {
            if (halts[x0]) continue;
            stamp++;
            if (stamp == 0) { memset(hstamp, 0, sizeof hstamp); stamp = 1; }
            i128 v = x0, y;
            long s;
            int outcome = 0; /* 1 halt, 2 cycle, 3 escape, 4 cap */
            for (s = 0; s < S; s++) {
                if (v <= N && halts[v]) { outcome = 1; break; }
                if (hinsert(v)) { outcome = 2; break; }
                if (!step(v, &y)) { outcome = 1; break; }
                if (y > LIM) { outcome = 3; break; }
                v = y;
            }
            if (!outcome) outcome = 4;
            if (outcome == 1) {
                /* replay and mark every small value on the path as halting */
                i128 w = x0;
                while (1) {
                    if (w <= N) { if (halts[w]) break; halts[w] = 1; }
                    if (!step(w, &y)) break;
                    w = y;
                }
            } else if (outcome == 2) {
                /* v is on the cycle: measure it */
                i128 w = v, mn = v; int per = 0;
                do { step(w, &w); per++; if (w < mn) mn = w; } while (w != v);
                int seen = 0;
                if (ncyc && mn == cyc_min) seen = 1;
                if (!seen) {
                    printf("CYCLE\t%s\tmin=", specbuf);
                    print128(mn);
                    printf("\tperiod=%d\tfrom=%ld\n", per, x0);
                    if (!ncyc || mn < cyc_min) { cyc_min = mn; cyc_per = per; }
                    ncyc++;
                    if (ncyc > 8) break;
                }
                /* mark the start's small path values as "done" so we do not re-report */
                i128 w2 = x0; long g = 0;
                while (g++ < S) { if (w2 <= N) { if (halts[w2]) break; halts[w2] = 1; } if (!step(w2, &w2)) break; }
            } else if (outcome == 3) {
                if (!esc_start) { esc_start = x0; esc_steps = s; }
            } else {
                if (!cap_start) cap_start = x0;
            }
        }
        (void)cyc_per;
        if (esc_start) printf("ESCAPE\t%s\tstart=%ld\tsteps=%ld\n", specbuf, esc_start, esc_steps);
        if (cap_start) printf("CAP\t%s\tstart=%ld\n", specbuf, cap_start);
        fflush(stdout);
    }
    return 0;
}
