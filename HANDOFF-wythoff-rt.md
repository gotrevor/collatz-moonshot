# HANDOFF: Theorem RT (residue-transitivity of the rational Wythoff members), DONE

Kickoff: `KICKOFF-2026-10-16-wythoff-rt.md`.  Branch `wip/wythoff-rt`.

## Status (2026-10-17)

`CollatzMoonshot/WythoffResidue.lean` is sorry-free; every ratified statement is unchanged
(checked against the ratify commit `03826cb`).  `#print axioms` on `residueTransitive_iff`,
`amusical_residueTransitive`, `amusical_eventually_mem_or_not_mem`,
`residueTransitive_absorbing_iff`, `two_minus_not_residueTransitive` and the window lemmas:
`[propext, Classical.choice, Quot.sound]`.  No `native_decide`, no axioms, no heartbeat bumps,
lines ≤ 100 characters.

## Route taken (differs from the kickoff's paper plan, simpler)

* **One drop lemma for every lift** (`ClassIn.drop`).  `ClassIn C K x` := `C` contains the class
  of `x` mod `K`.  If `f(x + K₁ A v) = f x + K₂ B v` for all `v` and `B` is coprime to `M / K₂`,
  then `ClassIn C K₁ x → ClassIn C K₂ (f x)` for closed `C`.  Instances:
  * fiber transport (`K₁ = K₂ = M'`), used by `residueTransitive_of_classIn`;
  * level drop (`K₁ = ℓ^{j+1} M'`, `K₂ = ℓ^j M'`), iterated by `exists_classIn_of_step`.
  No valuations or `lcm` bookkeeping: H4 collapsed to about 60 lines.
* A₂: `W`, multiplier `p` (odd).  B: `W⁻¹`, multiplier `2Q` (coprime to `ℓ ∣ p`).
  D: `W⁻¹`, with `p = 4p₄` dropping from `2^{j+1}·2M₀` to `2^j·2M₀`.
  A: `residueTransitive_lift_branch`, parametrized by the dropping parity `ε`.  If no class at
  the current level has an `ε`-point, the set `T` of residues mod `M'` carrying such a class is
  closed (routing by CRT along the keep-branch piece), so it contains `ε`, whose class does
  contain an `ε`-point: a contradiction.
* (B0): `residueTransitive_of_translate`.  An injective `g` with edges `x → g x` and
  `x → g x − u` (adjacent window indices) maps a closed `C` onto itself, so `C − u ⊆ C`.
* (B1): **counting replaces the circulation** (`exists_preimage_of_counting`).  The window maps
  `F_j` (even `x`) and `G_j` (odd `x`) are injective on their parity class.  This is where
  `p ≡ 2 (4) ∨ e = 1` enters, via `IsCoprime p' L`.  Non-absorbing gives an odd index in `J_E`
  and an even one in `J_O`, so `|C_E| ≤ |C_O| ≤ |C_E|`, and every window map is onto its
  parity part of `C`.  Then translate by `1/Q` on a window of length ≥ 3 (one of `q, R ≥ 3`).
* Assembly: `residueTransitive_of_lifts` (strong induction, `S` a divisor-closed modulus
  predicate, `good` the liftable primes), with `coprime_of_primes` for the base.
* Proof artifacts confirmed: Lemma B never uses `ℓ ∤ M'` or `0 < M'`, and Lemma A₂ never uses
  `M'` odd (unused-variable warnings on ratified signatures; left as is).

## Next

Nothing owed on this kickoff.  Possible follow-ups (not started): a `docs/notes/` note for
Theorem RT, and wiring `amusical_eventually_mem_or_not_mem` into the `AmusicalTrap` narrative.
