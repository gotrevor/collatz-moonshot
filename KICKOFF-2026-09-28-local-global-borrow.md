# Bounded theorem task: separate prime-power witnesses versus one integer witness

Own only `CollatzMoonshot/Obstructions/LocalGlobalBorrow23.lean` and
`HANDOFF-2026-09-28-local-global-borrow.md`.  Definitions and both statement
types are frozen.  Other agents own research notes and experiments.
This is an explicitly assigned elementary negative control under Trevor's
continuing research mandate, not a general Collatz proof campaign.

## Exact mechanism

For smaller input pair c=d=1, the cross equation at u=23 reduces to
`79*b=35`, with positive rational companion 35/79.  For c=13,d=17 it
reduces to `11*b=119`, with companion 119/11.  These are positive, odd
2-adic units and 3-adic units.

If p!=79 use (1,1).  If p=79 use (13,17).  The selected reduced
denominator is coprime to `6*p^k`, so solve the reduced equation modulo
`6*p^k`, e.g. with a modular inverse.  A least nonnegative solution plus
`6*p^k` is positive.  The reduced congruence modulo 6 forces b=5 mod6
in the first case and b=1 mod6 in the second.  Thus b is odd and not
divisible by 3.  Multiplying the reduced congruence by the canceled common
factor gives the exact cross congruence modulo p^k.

Alternative positive-residue construction: for the first pair set b=5+6t
and solve `79*t = -60 (mod p^k)`.  For the second set b=1+6t and solve
`11*t = 18 (mod p^k)`.  Modular inverse existence is the only input.

No p-adic topology or new imports beyond Mathlib are needed.  The frozen
negative theorem directly wraps `no_quadratic_cross_identity_23`.

The statement is intentionally `for every p,k there exists a witness`.
It does NOT assert simultaneous solvability for all moduli with the same
c,d,b, nor even solvability for every finite joint modulus.  A finite
joint modulus blocks all the small input pairs.  Do not call this a failure
of CRT or use it to claim that every local-to-global method fails.

Build module and root, quietly audit the two declarations, commit green,
and stop.  Handoff should report the quantifier obstruction and link the
research note; do not invent an unrelated optimization as the next target.
