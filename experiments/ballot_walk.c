// ballot_walk.c - C twin of `parity_reconstruction.py ballot-walk S K [THETA_U]` (about 100x
// faster; reached length 44 for k = 4 and length 50 for k = 8 on 2026-09-19).
//
// DFS over the (Phi, d) walk of a pair of starts x, x + k: A, B their shortcut-map
// trajectories, d = ones(w) - ones(u) so far, Phi = 3^d B - A, M = 3^max(0,-d) Phi (an
// integer); M even <=> the two parity letters agree.  Both words are kept exactly ballot
// (2^j <= 3^ones at every prefix); with a third argument THETA_U > 0 the second word may dip
// THETA_U bits below ballot.  Prints every j with Phi = 0, d = 0 (a same-shape coalescence
// of two ballot prefixes) and the node count.  Build: cc -O2 -o ballot_walk ballot_walk.c
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
typedef __int128 i128;
static int S; static long long K; static double THETA_U = 0.0; static const double L3 = 1.5849625007211563;
static i128 pow3[128]; static i128 pow2[128];
static unsigned long long nodes = 0; static int found = 0;
static char W[128], U[128];
static void rec(int j, i128 M, int d, int cw, int cu) {
    nodes++;
    if (M == 0 && d == 0 && j > 0) {
        W[j] = U[j] = 0;
        printf("COLLISION k=%lld j=%d a=%d\n  w=%s\n  u=%s\n", K, j, cw, W, U);
        fflush(stdout); found++;
    }
    if (j == S) return;
    int agree = ((M % 2) == 0);
    for (int wl = 1; wl >= 0; wl--) {
        int ul = agree ? wl : 1 - wl;
        int cw2 = cw + wl, cu2 = cu + ul;
        // ballot: 2^(j+1) <= 3^cw2 and 3^cu2
        if (pow2[j+1] > pow3[cw2]) continue;
        if (THETA_U == 0.0) { if (pow2[j+1] > pow3[cu2]) continue; }
        else { if (cu2 * L3 - (j + 1) < -THETA_U) continue; }
        i128 M2; int d2 = d;
        if (d >= 0) {
            if (wl == 1 && ul == 1)      M2 = (3*M + pow3[d] - 1) / 2;
            else if (wl == 0 && ul == 0) M2 = M / 2;
            else if (wl == 1 && ul == 0) { M2 = (3*M - 1) / 2; d2 = d + 1; }
            else { // (0,1)
                if (d >= 1) { M2 = (M + pow3[d-1]) / 2; d2 = d - 1; }
                else        { M2 = (3*M + 1) / 2; d2 = -1; }
            }
        } else {
            int e = -d;
            if (wl == 1 && ul == 1)      M2 = (3*M + 1 - pow3[e]) / 2;
            else if (wl == 0 && ul == 0) M2 = M / 2;
            else if (wl == 1 && ul == 0) { M2 = (M - pow3[e-1]) / 2; d2 = d + 1; }
            else                         { M2 = (3*M + 1) / 2; d2 = d - 1; }
        }
        W[j] = '0' + wl; U[j] = '0' + ul;
        rec(j + 1, M2, d2, cw2, cu2);
    }
}
int main(int argc, char **argv) {
    S = atoi(argv[1]); K = atoll(argv[2]); if (argc > 3) THETA_U = atof(argv[3]);
    pow3[0] = 1; pow2[0] = 1;
    for (int i = 1; i < 128; i++) { pow3[i] = pow3[i-1] * 3; pow2[i] = pow2[i-1] * 2; }
    // both words start with 1 (ballot); k even => first letters agree; M0 = k
    rec(0, (i128)K, 0, 0, 0);
    printf("k=%lld S=%d nodes=%llu collisions=%d\n", K, S, nodes, found);
    return 0;
}
