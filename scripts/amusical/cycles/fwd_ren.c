/* Ren's independent cycle-minimum search for the amusical permutation U (2026-10-13).
   Algorithm (different from the agent's lockstep U/V + meet-in-the-middle):
   for each n in [lo, hi], iterate U forward up to Pmax steps; stop on a value < n (n is not a
   minimum of a cycle of period <= Pmax, since a cycle would return before) or on a return to n
   (report).  If n is the minimum of a cycle of period P <= Pmax, its forward orbit stays > n until
   it returns at step P, so it is reported.  uint64 fast path, GMP once the value gets large.
   Usage: fwd_ren lo hi Pmax  -> prints "lo hi dips=.. returns=.. survivors=.. steps=.." and each return. */
#include <gmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
int main(int argc, char **argv) {
  uint64_t lo = strtoull(argv[1], 0, 10), hi = strtoull(argv[2], 0, 10);
  long Pmax = atol(argv[3]);
  mpz_t z; mpz_init(z);
  unsigned long long dips = 0, rets = 0, surv = 0, steps = 0;
  const uint64_t LIM = (UINT64_MAX / 3) - 4;
  for (uint64_t n = lo; n <= hi; n++) {
    uint64_t x = n; long j = 0; int big = 0, done = 0;
    while (j < Pmax) {
      if (!big) {
        if (x > LIM) { mpz_set_ui(z, x); big = 1; continue; }
        uint64_t r = x & 3;
        if ((x & 1) == 0) x = 3 * (x >> 1);
        else if (r == 1) x = 3 * (x >> 2) + 1;
        else x = 3 * (x >> 2) + 2;
        j++;
        if (x < n) { dips++; done = 1; break; }
        if (x == n) { rets++; printf("RETURN n=%llu period=%ld\n", (unsigned long long)n, j); done = 1; break; }
      } else {
        mp_limb_t l0 = mpz_getlimbn(z, 0);
        if ((l0 & 1) == 0) { mpz_tdiv_q_2exp(z, z, 1); mpz_mul_ui(z, z, 3); }
        else if ((l0 & 3) == 1) { mpz_tdiv_q_2exp(z, z, 2); mpz_mul_ui(z, z, 3); mpz_add_ui(z, z, 1); }
        else { mpz_tdiv_q_2exp(z, z, 2); mpz_mul_ui(z, z, 3); mpz_add_ui(z, z, 2); }
        j++;
        if (mpz_cmp_ui(z, n) < 0) { dips++; done = 1; break; }
        if (mpz_cmp_ui(z, n) == 0) { rets++; printf("RETURN n=%llu period=%ld\n", (unsigned long long)n, j); done = 1; break; }
        if (mpz_fits_ulong_p(z) && mpz_get_ui(z) <= LIM) { x = mpz_get_ui(z); big = 0; }
      }
    }
    steps += j;
    if (!done) surv++;
  }
  printf("RANGE %llu %llu Pmax=%ld dips=%llu returns=%llu survivors=%llu steps=%llu\n",
         (unsigned long long)lo, (unsigned long long)hi, Pmax, dips, rets, surv, steps);
  return 0;
}
