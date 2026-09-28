/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Descent

/-!
# MSP²: definitions

A Lean formalization of the MSP² framework of Mário Sousa Pereira and Enzo Mazzoni,
*"MSP² : une représentation regroupée des trajectoires de Syracuse"*, Revue Internationale
du Chercheur 7(3) (2026) 1071-1129, Zenodo `10.5281/zenodo.22555969`.  Section numbers
(`§n.m`) throughout refer to that article.

Everything here is stated over the repo's un-accelerated Collatz map
`CollatzMoonshot.step`, so the headline wires straight into `CollatzMoonshot.Conjecture`.
The article's own map is the grouped (Syracuse-style) step `msp2Step`; `covered_iff_msp2`
(in `MSP2.Proved`) records that the two notions of "covered" agree.
-/

namespace MSP2

open CollatzMoonshot

/-- The MSP² step (§2): halve an even value; send an odd `M` to `(3M+1)/2`
(written in the article as `(M+1)/2 · 3 − 1`). -/
def msp2Step (M : ℕ) : ℕ := if M % 2 = 0 then M / 2 else (3 * M + 1) / 2

/-- **Covered** (§16.1): the flight of `N` passes strictly below its starting value. -/
def Covered (N : ℕ) : Prop := ∃ j, step^[j] N < N

/-- The vertical rule of the Generator Table (§15.9) on a column `A·k + b`:
`b ↦ b/2` if `b` is even, `b ↦ (A+b)/2` if `b` is odd. -/
def tA (A b : ℕ) : ℕ := if b % 2 = 0 then b / 2 else (A + b) / 2

/-- The four representative families of rank `j` (§9.8):
`F_{j,s}(u) = A_j·u + 1 + s·A_j/4` with `A_j = 288·3^j`. -/
def famA (j : ℕ) : ℕ := 288 * 3 ^ j

def fam (j s u : ℕ) : ℕ := famA j * u + 1 + s * (famA j / 4)

/-- The block blocking points (§9.9): `B_0 = 25`, `B_{j+1} = 16·B_j − 15`. -/
def blockB : ℕ → ℕ
  | 0 => 25
  | j + 1 => 16 * blockB j - 15

/-- The "partie B" constants of §16.3-16.4: `B_0 = 4`, `B_{n+1} = 3·B_n + 1`
(4, 13, 40, 121, …), attached to the coefficient `A_n = 3^(n+2)`. -/
def bConst : ℕ → ℕ
  | 0 => 4
  | n + 1 => 3 * bConst n + 1

/-- The "cousin" jump offsets of §16.7.4, as the article's recurrence:
`Δ_0 = 2`, `Δ_{n+1} = −3·Δ_n − 10`. -/
def delta : ℕ → ℤ
  | 0 => 2
  | n + 1 => -3 * delta n - 10

/-- The second-optimisation left-route constants of §16.5 (1, 22, 13, 202, 121, 1822, …),
as the article's double recurrence `C_{n+2} = 9·C_n + 4`. -/
def cLeft : ℕ → ℕ
  | 0 => 1
  | 1 => 22
  | n + 2 => 9 * cLeft n + 4

/-- The negative-integer operator MSP²⁻ (§19): halve an even value; send an odd `U` to
`−(3(|U|−1)/2 + 1)`. -/
def msp2Neg (U : ℤ) : ℤ :=
  if U % 2 = 0 then U / 2 else -((3 * ((U.natAbs : ℤ) - 1)) / 2 + 1)

end MSP2
