# HANDOFF 2026-09-29 — cubic peel (scoped, closed)

Scope of this lap, per `KICKOFF-2026-09-29-cubic-peel.md`: own only
`CollatzMoonshot/Obstructions/CubicPeel.lean` and this handoff; prove exactly
the five frozen statements; root build green; stop.

## State: done, green, no sorries, no new axioms

`lake build` (root) completes; `CollatzMoonshot.lean` imports
`CollatzMoonshot.Obstructions.CubicPeel`. All five theorems are kernel-clean —
`#print axioms` shows only `propext` / `Quot.sound` / `Classical.choice`.

The five frozen statements (namespace
`CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair`):

1. `cubic_peel_value` — `certificateValue 0 [V,Q1,Q2] = certificateValue 0 [A,E1,E2]`
   for the affine families `cubicV/Q1/Q2/A/E1/E2` in `s`.  Via `odd_ratio`
   (from `FiveHead`) on each label, then one `div_eq_div_iff` cross-multiplication
   closed by `push_cast; ring`.
2. `cubic_peel_domain` — `cubicM s < cubicN s`; the four peel labels lie below
   `cubicM s`; and all seven labels are positive, odd, and 3-free.  `dsimp`/`omega`.
3. `cubic_peel_frontiers` — `tstep (cubicN s) = cubicA s` and
   `tstep (cubicV s) = 16 * cubicM s`, via `two_tstep_odd` then `omega`.
4. `cubic_peel_link` — `cubicN s = lowerN (recursiveH (16475 + 25172*s))`, by `ring`.
5. `cubic_peel_growth_congruence` — for every `j` there is `s` with
   `2^(j+2) ∣ 32327709860 + 49393127700*s`.

## The one new proof written this lap

`cubic_peel_growth_congruence` was the open `sorry`.  Discharged from a new
private lemma `odd_slope_hits (m a : ℕ) (hm : m % 2 = 1) : ∀ j, ∃ s, 2^j ∣ a + m*s`.
Rather than a `ZMod` modular inverse (the route the kickoff suggested via
`exists_linear_sol`), it is a direct lift-the-exponent induction in ℕ, which
avoids all cast bookkeeping: if `a + m*s = 2^j*k` and `k` is odd, then
`a + m*(s + 2^j) = 2^j*(k + m)` and `k + m` is even because `m` is odd, so the
witness for `j+1` is `s + 2^j` with cofactor `(k+m)/2`.  Each step is a `calc`
of `ring` identities, so nothing nonlinear reaches `omega`.

Applied with `m = 12348281925` (odd, hence coprime to every `2^j`) and
`a = 8081927465`; the factor-4 lift `2^j ∣ a + m*s → 2^(j+2) ∣ 4(a + m*s)` is a
`calc` chain `4*(2^j*k) = 2^(j+2)*k`.

## Repair to the pre-existing `cubic_peel_value` skeleton

The skeleton's `div_eq_div_iff` side conditions were associated as
`mul_ne_zero (mul_ne_zero _ _) _`, but `List.prod_cons` leaves the denominators
right-nested, so after the `div_mul_div_comm` rewrites the actual shape is
`(3V+1) * ((3Q1+1) * (3Q2+1))`.  Changed to
`mul_ne_zero (hne _) (mul_ne_zero (hne _) (hne _))`.  Worth remembering: the
nesting of the `≠ 0` witness must match `prod_cons` right-association.

## Numerical cross-check (outside Lean, for the record)

With `a = cubicA s`, the kickoff's coefficient formulas reproduce the actual
`Nat` defs exactly: `v = 5a-2`, `q1 = (3a-1)/64`, `q2 = 5(2a-7)/93`,
`e1 = (3a+1)/58`, `e2 = (2a-7)/21`, checked at `s = 0,1,7`.  The two odd-ratio
products do agree, as `cubic_peel_value` proves.  One correction to the kickoff
prose: their common value is `(2a-7)/(6(9a+61))`, not `4(2a-7)/(3(9a+61))` —
the latter is 8× too large.  No Lean statement asserts the closed form, so this
is a note on the prose only.

## Deliberately not claimed

No restricted replay, no full repair, no balanced certificate, no termination or
trajectory convergence.  These five are positive scalar / domain / frontier /
congruence statements about one CRT subclass, and `cubic_peel_growth_congruence`
in particular is a statement about the arithmetic progression alone — it says
nothing about any orbit.  This subclass is *not* the fixed C5 rule of
`AllowedMove`.  The shortcut prefix formula that would turn statement 5 into a
dynamics claim is a separate lemma and was not attempted here.

No Aristotle job was run; no follow-up targets invented.  Parent session owns
all other source and docs.
