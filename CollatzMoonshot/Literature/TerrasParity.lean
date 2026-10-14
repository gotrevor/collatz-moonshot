/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import CollatzMoonshot.FrontB.Dictionary

/-!
# Terras's parity-vector bijection (literature)

The first `k` parities of the shortcut orbit `tstep` depend only on `n mod 2^k`, and every
pattern of `k` parities occurs for exactly one residue class mod `2^k`.  This is the finite form
of the 2-adic conjugacy between `tstep` and the one-sided shift (Lagarias 1985): Haar-almost
every 2-adic start has a normal parity sequence, so its odd share is `1/2 < log 2 / log 3`.
The positive integers are a null set, which is the gap between this fact and `Conjecture`.

Sources: R. Terras, *A stopping time problem on the positive integers*, Acta Arith. 30 (1976)
241-252; C. J. Everett, *Iteration of the number-theoretic function f(2n) = n,
f(2n+1) = 3n+2*, Adv. Math. 25 (1977) 42-45; J. C. Lagarias, *The 3x+1 problem and its
generalizations*, Amer. Math. Monthly 92 (1985) 3-23.  Transcribed from memory on 2026-10-12;
check the statement against Terras before citing it outward.
-/

namespace CollatzMoonshot.Literature

open CollatzMoonshot.FrontB

/-- The first `k` parities of the shortcut orbit of `n` (`true` = odd). -/
def parityVector (k n : ℕ) : Fin k → Bool :=
  fun i => decide (tstep^[i.val] n % 2 = 1)

/-- **[Literature: Terras 1976, Everett 1977]**  The length-`k` parity vector depends only on
`n mod 2^k`, and on residues mod `2^k` it is a bijection onto all `2^k` patterns. -/
def TerrasParityBijection : Prop :=
  (∀ k n : ℕ, parityVector k n = parityVector k (n % 2 ^ k)) ∧
    ∀ k : ℕ, Function.Bijective fun r : Fin (2 ^ k) => parityVector k r.val

end CollatzMoonshot.Literature
