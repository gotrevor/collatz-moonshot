/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.FrontA.BackwardTwoThirds

/-!
# Pinned experimental target: correlated exponent 3/4

This file freezes the exact local theorem found by the barrier-transfer
experiment. The treadmill may add helper definitions and lemmas, but must not
weaken the definitions or acceptance theorem below. It deliberately starts
with one unresolved proof and is not imported by CollatzMoonshot.lean until proved.
-/

namespace CollatzMoonshot.FrontA

/-! ## Five endpoint/floor height states: 1, 7/4, 3, 6, 12 -/

def threeQuartersHeightNum (i : Fin 5) : ℕ :=
  if i.1 = 0 then 1 else if i.1 = 1 then 7 else if i.1 = 2 then 3
  else if i.1 = 3 then 6 else 12

def threeQuartersHeightDen (i : Fin 5) : ℕ :=
  if i.1 = 1 then 4 else 1

def InThreeQuartersHeightState (d : ℕ) (i : Fin 5) (x : ℕ) : Prop :=
  threeQuartersHeightNum i * d ≤ threeQuartersHeightDen i * x

/-- For a growing edge of cost j ≥ 2, the floor index advances by
j - 2, capped at the top state. -/
def nextThreeQuartersState (i : Fin 5) (j : ℕ) : Fin 5 :=
  ⟨min (i.1 + (j - 2)) 4, by omega⟩

/-- The safe shrinking edge drops exactly one floor state. -/
def shrinkThreeQuartersState (i : Fin 5) : Fin 5 :=
  ⟨i.1 - 1, by omega⟩

def threeQuartersHasShrink (i : Fin 5) (r : ℕ) : Bool :=
  decide (1 ≤ i.1) && (r % 9 == 2 || r % 9 == 8)

/-! ## Frozen 810-state potential

Order: height state outermost, then the 162 positive unit residues modulo 243
in increasing order. For a unit residue r = 3q+1 its zero-based index is 2q;
for r = 3q+2 it is 2q+1.
-/

def threeQuartersUnitIndex (r : ℕ) : ℕ :=
  2 * (r / 3) + if r % 3 = 2 then 1 else 0

set_option maxRecDepth 10000 in
def threeQuartersWeights : Array ℕ := #[
  5620241, 2507527, 3120869, 3594000, 2733565, 1519851, 3988049, 4200861, 1575034,
  3728847, 2556089, 1151736, 3957839, 1982248, 2633593, 3244528, 1837253, 1166946,
  4669019, 2209771, 4393798, 4265757, 1936993, 1632640, 4346694, 2774639, 1611259,
  3417814, 3231598, 1592286, 4786053, 2537186, 3552608, 3089897, 1962573, 1116127,
  5230181, 2318676, 3621694, 3629770, 2437381, 2312784, 5989602, 4019530, 1924277,
  3191331, 2745779, 1628117, 4756914, 3085015, 2172146, 3129179, 1681803, 1151424,
  4664483, 2835167, 4250585, 4566439, 2677912, 1688767, 2747974, 4373230, 1993314,
  3093145, 2783384, 1099490, 5141104, 1635142, 2968143, 3202303, 1877105, 1045486,
  6084338, 2333835, 3899557, 3972764, 1855553, 1873211, 4105507, 3782885, 1537297,
  3858188, 3089640, 1634936, 4862954, 2722793, 3799060, 3005190, 1929196, 1092430,
  4488548, 2612552, 3356852, 4067300, 2554673, 1921508, 6480411, 4215861, 1972128,
  3109866, 2802573, 1449267, 4774924, 2921251, 2790263, 2828461, 1936469, 1000000,
  5620973, 2655402, 3928948, 2637009, 2491042, 1655000, 3499971, 3885783, 1614337,
  4182946, 2840173, 1103312, 4684206, 1602291, 2981782, 2957116, 2076895, 1147100,
  3850026, 1995984, 3797237, 4369645, 1849126, 2188851, 4612354, 5050888, 1449099,
  3503410, 2381301, 1771183, 4507000, 2125448, 2879756, 3156921, 1758301, 1234922,
  4910136, 2780278, 3797265, 4531573, 2083128, 1777770, 5495385, 3562362, 2274287,
  3120674, 3150372, 1238628, 4840945, 3480021, 3097188, 3110857, 1849716, 1099841,
  6488712, 9452282, 4217166, 5196165, 2749641, 5248892, 6044400, 8178893, 4579202,
  4597318, 2556089, 6389398, 5054137, 6707481, 7065021, 3244528, 1837253, 2648953,
  6271185, 7549045, 4393798, 4298839, 1936993, 5645621, 6840397, 6656830, 3333751,
  4296456, 3231598, 4429260, 5456657, 10899463, 7090247, 3089897, 1962573, 3316769,
  5230181, 7852505, 3716400, 4713376, 2437381, 7389619, 7174162, 8030982, 4912969,
  3257640, 2745779, 4692785, 4756914, 7311024, 4666395, 3256759, 1681803, 2709848,
  5748089, 9453559, 4465864, 5434910, 2677912, 6607792, 4434930, 8049557, 4267046,
  4189442, 2783384, 5974900, 5196597, 5886565, 6535121, 3300661, 1877105, 2715037,
  7034891, 8796398, 3899557, 4776612, 1855553, 6091044, 6104557, 7878291, 2694737,
  4099194, 3889646, 5014842, 4973287, 10073757, 6760057, 3492928, 1929196, 3236295,
  5367190, 6475113, 3356852, 4617860, 2738171, 6386366, 7348882, 8000776, 5188386,
  3109866, 3681216, 3653281, 5262662, 7757623, 8494599, 2828461, 1936469, 2437126,
  5892046, 7844869, 4768192, 4004878, 2978780, 7148759, 7679850, 7580270, 3574585,
  4503719, 2840173, 4843258, 5309318, 4621823, 7354910, 2957116, 2076895, 3352408,
  5202060, 8258099, 4675879, 4681104, 1849126, 6386316, 7621213, 8646801, 2749987,
  3503410, 2989859, 4991917, 5385642, 9242846, 5991191, 3156921, 1758301, 3824930,
  5248358, 10232784, 3925050, 5298305, 2083128, 6558398, 6681406, 8142052, 5852709,
  3120674, 3150372, 5208974, 5231849, 6905165, 6362068, 3110857, 1849716, 2585457,
  6894037, 10912879, 5037445, 6541619, 2749641, 7092648, 8738926, 8364417, 8773118,
  4624354, 2556089, 11369212, 5874416, 10165798, 7996720, 3244528, 1837253, 7701370,
  7731782, 9026748, 4393798, 4298839, 1936993, 5645621, 7766330, 8500586, 7362220,
  4605064, 3231598, 11882041, 5456657, 12360060, 7146050, 3089897, 1962573, 8725882,
  5230181, 10547033, 3716400, 6191079, 2437381, 7389619, 7229799, 8851261, 6390672,
  3257640, 2745779, 14286354, 4756914, 11504940, 6940250, 3256759, 1681803, 5606738,
  7225792, 9909450, 4465864, 5434910, 2677912, 8019248, 6735416, 9177388, 9490808,
  5009721, 2783384, 11924483, 5196597, 12916299, 8357533, 3300661, 1877105, 6011785,
  7574368, 8796398, 3899557, 4776612, 1855553, 6250316, 7926969, 8929589, 4288083,
  4099194, 3889646, 12369589, 4973287, 12065953, 7402008, 3492928, 1929196, 8262685,
  5478709, 8748968, 3356852, 4617860, 2738171, 7864070, 7872694, 8000776, 5188386,
  3109866, 3928034, 7848114, 5477226, 12818016, 10093242, 2828461, 1936469, 4624966,
  5892046, 9667280, 4768192, 5028354, 3139192, 7510907, 9140448, 9057973, 6936591,
  4503719, 2840173, 10076079, 5309318, 7458950, 8815507, 2957116, 2076895, 7176377,
  7045816, 8826894, 4751989, 4681104, 1849126, 6601230, 8910705, 8740188, 5429408,
  3503410, 3810139, 10990861, 5551060, 11237500, 7468895, 3156921, 1758301, 9843131,
  5248358, 11831427, 3925050, 5298305, 2083128, 6558398, 8033319, 8799476, 6164362,
  3120674, 3150372, 10699860, 5231849, 10267174, 9056595, 3110857, 1849716, 4532044,
  6894037, 11594601, 5322918, 6541619, 2749641, 8472195, 11001713, 8364417, 10326103,
  4624354, 2556089, 12448831, 5874416, 14697460, 7996720, 3244528, 1837253, 14754711,
  7777252, 9214286, 4393798, 4298839, 1936993, 5645621, 7766330, 9880133, 7710202,
  4605064, 3231598, 13448986, 5456657, 13240765, 7146050, 3089897, 1962573, 8725882,
  5230181, 13003470, 3716400, 6606180, 2437381, 7389619, 7229799, 9212171, 6742852,
  3257640, 2745779, 16974956, 4756914, 13062211, 10041083, 3256759, 1681803, 12381828,
  7744811, 9909450, 4465864, 5434910, 2677912, 8019248, 8456701, 9177388, 11496029,
  5279502, 2783384, 12018348, 5196597, 15372735, 10842739, 3300661, 1877105, 11666016,
  7574368, 8796398, 3899557, 4776612, 1855553, 6250316, 10412175, 8929589, 6435760,
  4099194, 3889646, 14826025, 4973287, 12159456, 7402008, 3492928, 1929196, 10747890,
  5478709, 11849802, 3356852, 4617860, 2738171, 7992089, 7872694, 8000776, 5188386,
  3109866, 3928034, 11672289, 5477226, 14986603, 10713364, 2828461, 1936469, 9131220,
  5892046, 12152486, 4768192, 6407902, 3139192, 7510907, 9140448, 9336133, 10001529,
  4503719, 2840173, 12561285, 5309318, 11327913, 9227373, 2957116, 2076895, 15961726,
  8425364, 8826894, 4751989, 4681104, 1849126, 6601230, 8910705, 8740188, 9961069,
  3503410, 3810139, 14055799, 5551060, 13511174, 7699875, 3156921, 1758301, 10367269,
  5248358, 12738738, 3925050, 5298305, 2083128, 6558398, 8033319, 8799476, 6164362,
  3120674, 3150372, 15231525, 5231849, 13332111, 11205314, 3110857, 1849716, 7211738,
  6894037, 11594601, 5322918, 6541619, 2749641, 8952266, 11001713, 8364417, 10326103,
  4624354, 2556089, 12448831, 5874416, 18503081, 7996720, 3244528, 1837253, 17366526,
  7777252, 9214286, 4393798, 4298839, 1936993, 5645621, 7766330, 9880133, 7710202,
  4605064, 3231598, 13448986, 5456657, 13240765, 7146050, 3089897, 1962573, 8725882,
  5230181, 13079938, 3716400, 6606180, 2437381, 7389619, 7229799, 9212171, 6742852,
  3257640, 2745779, 18017896, 4756914, 13062211, 12361211, 3256759, 1681803, 12967068,
  7744811, 9909450, 4465864, 5434910, 2677912, 8019248, 10776828, 9177388, 11496029,
  5279502, 2783384, 12018348, 5196597, 15372735, 11495168, 3300661, 1877105, 16820637,
  7574368, 8796398, 3899557, 4776612, 1855553, 6250316, 11110292, 8929589, 9330623,
  4099194, 3889646, 15518704, 4973287, 12159456, 7402008, 3492928, 1929196, 11340183,
  5478709, 14169929, 3356852, 4617860, 2738171, 7992089, 7872694, 8000776, 5188386,
  3109866, 3928034, 16887280, 5477226, 14986603, 10713364, 2828461, 1936469, 16752581,
  5892046, 13025379, 4768192, 6407902, 3139192, 7510907, 9140448, 9336133, 14181155,
  4503719, 2840173, 12949752, 5309318, 14222775, 9227373, 2957116, 2076895, 19334101,
  8879081, 8826894, 4751989, 4681104, 1849126, 6601230, 8910705, 8740188, 14092311,
  3503410, 3810139, 18235425, 5551060, 13511174, 7699875, 3156921, 1758301, 10367269,
  5248358, 12738738, 3925050, 5298305, 2083128, 6558398, 8033319, 8799476, 6164362,
  3120674, 3150372, 18845234, 5231849, 17511738, 11205314, 3110857, 1849716, 10823707,

]

def threeQuartersPotential (i : Fin 5) (r : ℕ) : ℕ :=
  (threeQuartersWeights[
    i.1 * 162 + threeQuartersUnitIndex (r % 243)]?).getD 0

/-- The elementary exact comparisons behind the rational 3/4 edge
underweight. -/
theorem threeQuartersRationalUnderestimate :
    (2279 / 1000 : ℚ) ^ 4 < 27 ∧
      8 * (2973 / 5000 : ℚ) ^ 4 < 1 := by
  norm_num

/-! ## Height-state helpers and floor-safe transitions -/

/-- Every height floor is at least `1`, so every state stays above `d`. -/
theorem InThreeQuartersHeightState.le {d x : ℕ} {i : Fin 5}
    (h : InThreeQuartersHeightState d i x) : d ≤ x := by
  unfold InThreeQuartersHeightState threeQuartersHeightNum threeQuartersHeightDen at h
  fin_cases i <;> simp_all <;> omega

/-- Floor-safe five-state transition for an actual growing odd block of cost
`j ≥ 2`: the floor index advances by `j - 2`, capped at the top state. -/
theorem threeQuartersHeightStep_growing {d x y j : ℕ} {i : Fin 5} (hd : 2 ≤ d)
    (hj : 2 ≤ j) (hstate : InThreeQuartersHeightState d i x)
    (hblock : 3 * y + 1 = 2 ^ j * x) :
    InThreeQuartersHeightState d (nextThreeQuartersState i j) y := by
  have hxd : d ≤ x := InThreeQuartersHeightState.le hstate
  rcases Nat.lt_or_ge j 6 with hj6 | hj6
  · simp only [InThreeQuartersHeightState, threeQuartersHeightNum,
      threeQuartersHeightDen] at hstate
    interval_cases j <;>
      · norm_num at hblock
        simp only [InThreeQuartersHeightState, nextThreeQuartersState,
          threeQuartersHeightNum, threeQuartersHeightDen]
        fin_cases i <;> simp_all <;> omega
  · have hnext : nextThreeQuartersState i j = ⟨4, by omega⟩ := by
      apply Fin.ext
      simp only [nextThreeQuartersState]
      omega
    have h64 : (64 : ℕ) ≤ 2 ^ j := by
      calc (64 : ℕ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj6
    have h64x : 64 * x ≤ 3 * y + 1 := by
      rw [hblock]; exact Nat.mul_le_mul_right x h64
    rw [hnext]
    unfold InThreeQuartersHeightState threeQuartersHeightNum threeQuartersHeightDen
    norm_num
    omega

/-- Floor-safe five-state transition for the actual shrinking `j = 1` block,
which drops exactly one floor state. -/
theorem threeQuartersHeightStep_shrinking {d x y : ℕ} {i : Fin 5} (hd : 2 ≤ d)
    (hi : 1 ≤ i.1) (hstate : InThreeQuartersHeightState d i x)
    (hblock : 3 * y + 1 = 2 * x) :
    InThreeQuartersHeightState d (shrinkThreeQuartersState i) y := by
  simp only [InThreeQuartersHeightState, shrinkThreeQuartersState,
    threeQuartersHeightNum, threeQuartersHeightDen] at hstate ⊢
  fin_cases i <;> simp_all <;> omega

/-! ## The shared next ternary digit (source mod 729, child mod 243) -/

/-- The child residue modulo `243` determined by the source modulo `729`,
including the fixed carry digit produced by the division `(2^j r - 1) / 3`. -/
def threeQuartersChildResidue (r j : ℕ) : ℕ :=
  ((2 ^ j * (r % 729) - 1) / 3) % 243

/-- An actual odd inverse block has the child residue predicted by
`threeQuartersChildResidue`. -/
theorem oddBlockChild_mod_243 {x y j : ℕ}
    (h : 3 * y + 1 = 2 ^ j * x) :
    y % 243 = threeQuartersChildResidue x j := by
  unfold threeQuartersChildResidue
  have hx : x % 729 + 729 * (x / 729) = x := Nat.mod_add_div x 729
  have hp : 0 < 2 ^ j := pow_pos (by omega) _
  have heq :
      3 * y + 1 =
        2 ^ j * (x % 729) + 729 * (2 ^ j * (x / 729)) := by
    calc
      3 * y + 1 = 2 ^ j * x := h
      _ = 2 ^ j * (x % 729 + 729 * (x / 729)) :=
        congrArg (fun z => 2 ^ j * z) hx.symm
      _ = 2 ^ j * (x % 729) + 729 * (2 ^ j * (x / 729)) := by ring
  have hr : 0 < x % 729 := by
    by_contra hz
    have hz' : x % 729 = 0 := Nat.eq_zero_of_not_pos hz
    rw [hz', mul_zero, zero_add] at heq
    omega
  have hpr : 0 < 2 ^ j * (x % 729) := Nat.mul_pos hp hr
  let z := 2 ^ j * (x / 729)
  have hzle : 243 * z ≤ y := by dsimp [z]; omega
  have hnum : 2 ^ j * (x % 729) - 1 = 3 * (y - 243 * z) := by dsimp [z]; omega
  have ha : (2 ^ j * (x % 729) - 1) / 3 = y - 243 * z := by rw [hnum]; omega
  rw [ha]; omega

/-- The child residue seen from a state residue modulo `243` together with one
shared next ternary digit `t` of the source. -/
def threeQuartersSharedLift (r j t : ℕ) : ℕ :=
  threeQuartersChildResidue (r % 243 + 243 * (t % 3)) j

/-- The single shared digit `t = x / 243 % 3` really controls every actual
child: an odd block from `x` lands in the residue class it selects. -/
theorem oddBlockChild_sharedLift_243 {x y j : ℕ}
    (h : 3 * y + 1 = 2 ^ j * x) :
    y % 243 = threeQuartersSharedLift x j (x / 243 % 3) := by
  rw [oddBlockChild_mod_243 h]
  unfold threeQuartersSharedLift threeQuartersChildResidue
  have h729 : (x % 243 + 243 * (x / 243 % 3 % 3)) % 729 = x % 729 := by omega
  rw [h729]

theorem threeQuartersSharedLift_mod_left (x j t : ℕ) :
    threeQuartersSharedLift (x % 243) j t = threeQuartersSharedLift x j t := by
  unfold threeQuartersSharedLift
  rw [Nat.mod_mod_of_dvd x dvd_rfl]

theorem threeQuartersSharedLift_mod_right (x j t : ℕ) :
    threeQuartersSharedLift x j (t % 3) = threeQuartersSharedLift x j t := by
  unfold threeQuartersSharedLift
  rw [Nat.mod_mod_of_dvd t dvd_rfl]

/-! ## Potential helpers -/

/-- The state potential depends only on the residue modulo `243`. -/
theorem threeQuartersPotential_mod (i : Fin 5) (x : ℕ) :
    threeQuartersPotential i (x % 243) = threeQuartersPotential i x := by
  unfold threeQuartersPotential
  rw [Nat.mod_mod_of_dvd x dvd_rfl]

/-- Every reusable residue has strictly positive potential at every floor. -/
theorem threeQuartersPotential_pos_of_unit :
    ∀ i : Fin 5, ∀ r : Fin 243, r.1 % 3 ≠ 0 →
      0 < threeQuartersPotential i r.1 := by
  native_decide

theorem sevenCostsAt_mod_243 (x : ℕ) :
    sevenCostsAt (x % 243) = sevenCostsAt x := by
  unfold sevenCostsAt
  rw [Nat.mod_mod_of_dvd x (by norm_num : 9 ∣ 243)]

theorem threeQuartersHasShrink_mod_243 (i : Fin 5) (x : ℕ) :
    threeQuartersHasShrink i (x % 243) = threeQuartersHasShrink i x := by
  unfold threeQuartersHasShrink
  rw [Nat.mod_mod_of_dvd x (by norm_num : 9 ∣ 243)]

/-! ## The kernel/native-checked integer certificate -/

/-- One integer-scaled growing edge of the transfer image: the true edge
weight `(2279/1000)·(2973/5000)^j` is cleared to scale `1000 · 5000^23`. -/
def threeQuartersNatEdge (i : Fin 5) (r t j : ℕ) : ℕ :=
  2973 ^ j * 5000 ^ (23 - j) *
    threeQuartersPotential (nextThreeQuartersState i j)
      (threeQuartersSharedLift r j t)

/-- The integer-scaled one-generation transfer image at one source lift. -/
def threeQuartersNatImage (i : Fin 5) (r t : ℕ) : ℕ :=
  2279 * (threeQuartersNatEdge i r t (sevenCostsAt r 0) +
    threeQuartersNatEdge i r t (sevenCostsAt r 1) +
    threeQuartersNatEdge i r t (sevenCostsAt r 2) +
    threeQuartersNatEdge i r t (sevenCostsAt r 3) +
    threeQuartersNatEdge i r t (sevenCostsAt r 4) +
    threeQuartersNatEdge i r t (sevenCostsAt r 5) +
    threeQuartersNatEdge i r t (sevenCostsAt r 6) +
    if threeQuartersHasShrink i r then
      2973 * 5000 ^ 22 *
        threeQuartersPotential (shrinkThreeQuartersState i)
          (threeQuartersSharedLift r 1 t)
    else 0)

/-- All `810 × 3 = 2430` source-state/lift inequalities of the frozen
certificate, in integer form at scale `1000 · 5000^23`. -/
theorem threeQuartersNatCertificate :
    ∀ i : Fin 5, ∀ t : Fin 3, ∀ r : Fin 243, r.1 % 3 ≠ 0 →
      1000 * 5000 ^ 23 * threeQuartersPotential i r.1 <
        threeQuartersNatImage i r.1 t.1 := by
  native_decide

/-! ## The rational certificate -/

/-- The rational one-generation transfer image at one source lift, with the
exact edge underweight `(2279/1000) · (2973/5000)^j`. -/
def threeQuartersImage (i : Fin 5) (r t : ℕ) : ℚ :=
  (2279 / 1000 : ℚ) *
    (∑ k : Fin 7, (2973 / 5000 : ℚ) ^ sevenCostsAt r k *
        threeQuartersPotential (nextThreeQuartersState i (sevenCostsAt r k))
          (threeQuartersSharedLift r (sevenCostsAt r k) t) +
      if threeQuartersHasShrink i r then
        (2973 / 5000 : ℚ) *
          threeQuartersPotential (shrinkThreeQuartersState i)
            (threeQuartersSharedLift r 1 t)
      else 0)

theorem threeQuartersImage_mod (i : Fin 5) (x t : ℕ) :
    threeQuartersImage i (x % 243) (t % 3) = threeQuartersImage i x t := by
  unfold threeQuartersImage
  simp only [sevenCostsAt_mod_243, threeQuartersSharedLift_mod_left,
    threeQuartersSharedLift_mod_right, threeQuartersHasShrink_mod_243]

private theorem qpow_scale_3q {j : ℕ} (hj : j ≤ 23) :
    ((2973 : ℚ) / 5000) ^ j * 5000 ^ 23 = 2973 ^ j * 5000 ^ (23 - j) := by
  have hsplit : (5000 : ℚ) ^ 23 = 5000 ^ j * 5000 ^ (23 - j) := by
    rw [← pow_add]; congr 1; omega
  have hcancel : ((2973 : ℚ) / 5000) ^ j * 5000 ^ j = 2973 ^ j := by
    rw [div_pow]; field_simp
  rw [hsplit, ← mul_assoc, hcancel]

/-- The integer-scaled image is exactly `1000 · 5000^23` times the rational
image. -/
theorem threeQuartersNatImage_eq (i : Fin 5) (r t : ℕ) :
    (threeQuartersNatImage i r t : ℚ) =
      1000 * 5000 ^ 23 * threeQuartersImage i r t := by
  have h0 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 0)
  have h1 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 1)
  have h2 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 2)
  have h3 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 3)
  have h4 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 4)
  have h5 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 5)
  have h6 := qpow_scale_3q (sevenCostsAt_le_twentyThree r 6)
  unfold threeQuartersNatImage threeQuartersNatEdge threeQuartersImage
  rw [Fin.sum_univ_seven]
  by_cases hs : threeQuartersHasShrink i r = true <;>
    simp only [hs, if_true, Bool.false_eq_true, if_false] <;>
    push_cast <;>
    rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6] <;>
    ring

/-- The rational certificate at an arbitrary reusable source and arbitrary
shared lift digit. -/
theorem threeQuartersPotentialCertificateAt (i : Fin 5) {x : ℕ} (h3 : ¬3 ∣ x)
    (t : ℕ) : (threeQuartersPotential i x : ℚ) < threeQuartersImage i x t := by
  have hr243 : x % 243 < 243 := Nat.mod_lt x (by norm_num)
  have hru : (x % 243) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd x (by norm_num : 3 ∣ 243)]
    exact fun h0 => h3 (Nat.dvd_of_mod_eq_zero h0)
  have hnat := threeQuartersNatCertificate i ⟨t % 3, Nat.mod_lt t (by norm_num)⟩
    ⟨x % 243, hr243⟩ hru
  have hq : (threeQuartersPotential i (x % 243) : ℚ) <
      threeQuartersImage i (x % 243) (t % 3) := by
    have hcast :
        ((1000 * 5000 ^ 23 * threeQuartersPotential i (x % 243) : ℕ) : ℚ) <
        (threeQuartersNatImage i (x % 243) (t % 3) : ℚ) := by
      exact_mod_cast hnat
    rw [threeQuartersNatImage_eq] at hcast
    push_cast at hcast
    have hpos : (0 : ℚ) < 1000 * 5000 ^ 23 := by norm_num
    exact lt_of_mul_lt_mul_left (by linarith) (le_of_lt hpos)
  rw [threeQuartersPotential_mod, threeQuartersImage_mod] at hq
  exact hq

/-- Pinned correlated exponent-3/4 local expansion target.

Every reusable source in one of the five height states has the exact seven
distinct growing odd children, plus the actual safe shrinking child precisely
when enabled. The actual children remain in the claimed height states and the
frozen potential strictly expands with the rational edge underweight.
-/
theorem exists_threeQuartersExpansion {d x : ℕ} (i : Fin 5) (hd : 2 ≤ d)
    (hx : 2 ≤ x) (h3 : ¬3 ∣ x)
    (hstate : InThreeQuartersHeightState d i x) :
    ∃ (ys : Fin 7 → ℕ) (z : ℕ), Function.Injective ys ∧
      (∀ k, GrowingUnitOddBlockChild x (ys k) (sevenCostsAt x k) ∧
        InThreeQuartersHeightState d
          (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) ∧
        3 * ys k < 2 ^ 23 * x) ∧
      (threeQuartersHasShrink i x = true →
        UnitOddBlockChildAtOne x z ∧
        InThreeQuartersHeightState d (shrinkThreeQuartersState i) z ∧
        ∀ k, z ≠ ys k) ∧
      (threeQuartersPotential i x : ℚ) <
        (2279 / 1000 : ℚ) *
          (∑ k : Fin 7, (2973 / 5000 : ℚ) ^ sevenCostsAt x k *
              threeQuartersPotential
                (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) +
            if threeQuartersHasShrink i x then
              (2973 / 5000 : ℚ) *
                threeQuartersPotential (shrinkThreeQuartersState i) z
            else 0) := by
  obtain ⟨ys, hys, hch⟩ := exactSevenCostTransferAt hx h3
  have hcert := threeQuartersPotentialCertificateAt i h3 (x / 243 % 3)
  have hgrow : ∀ k, GrowingUnitOddBlockChild x (ys k) (sevenCostsAt x k) ∧
      InThreeQuartersHeightState d
        (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) ∧
      3 * ys k < 2 ^ 23 * x := by
    intro k
    refine ⟨hch k,
      threeQuartersHeightStep_growing hd (hch k).1 hstate (hch k).2.2.2.2, ?_⟩
    have hc := sevenCostsAt_le_twentyThree x k
    have hple : (2 : ℕ) ^ sevenCostsAt x k ≤ 2 ^ 23 :=
      Nat.pow_le_pow_right (by norm_num) hc
    have hmul : 2 ^ sevenCostsAt x k * x ≤ 2 ^ 23 * x :=
      Nat.mul_le_mul_right x hple
    have hb := (hch k).2.2.2.2
    omega
  have hpotEq : ∀ k : Fin 7,
      threeQuartersPotential (nextThreeQuartersState i (sevenCostsAt x k))
        (threeQuartersSharedLift x (sevenCostsAt x k) (x / 243 % 3)) =
      threeQuartersPotential (nextThreeQuartersState i (sevenCostsAt x k))
        (ys k) := by
    intro k
    rw [← oddBlockChild_sharedLift_243 (hch k).2.2.2.2, threeQuartersPotential_mod]
  by_cases hs : threeQuartersHasShrink i x = true
  · have hrem : x % 9 = 2 ∨ x % 9 = 8 := by
      unfold threeQuartersHasShrink at hs
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hs
      exact hs.2
    have hi1 : 1 ≤ i.1 := by
      unfold threeQuartersHasShrink at hs
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
        decide_eq_true_eq] at hs
      exact hs.1
    obtain ⟨z, hz⟩ := exists_unitOddBlockChildAtOne hrem
    have hzblock : 3 * z + 1 = 2 ^ 1 * x := by
      have := hz.2.2.2; norm_num; omega
    have hz243 :
        threeQuartersPotential (shrinkThreeQuartersState i)
          (threeQuartersSharedLift x 1 (x / 243 % 3)) =
        threeQuartersPotential (shrinkThreeQuartersState i) z := by
      rw [← oddBlockChild_sharedLift_243 hzblock, threeQuartersPotential_mod]
    refine ⟨ys, z, hys, hgrow, fun _ =>
      ⟨hz, threeQuartersHeightStep_shrinking hd hi1 hstate hz.2.2.2,
        fun k hzy => ?_⟩, ?_⟩
    · have hzlt := hz.2.2.1
      have hylt := (hch k).2.2.2.1
      omega
    · have himg : threeQuartersImage i x (x / 243 % 3) =
          (2279 / 1000 : ℚ) *
            (∑ k : Fin 7, (2973 / 5000 : ℚ) ^ sevenCostsAt x k *
                threeQuartersPotential
                  (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) +
              if threeQuartersHasShrink i x then
                (2973 / 5000 : ℚ) *
                  threeQuartersPotential (shrinkThreeQuartersState i) z
              else 0) := by
        unfold threeQuartersImage
        rw [Finset.sum_congr rfl fun k _ => by rw [hpotEq k]]
        simp only [hs, if_true, hz243]
      exact himg ▸ hcert
  · refine ⟨ys, 0, hys, hgrow, fun hcontra => absurd hcontra hs, ?_⟩
    have himg : threeQuartersImage i x (x / 243 % 3) =
        (2279 / 1000 : ℚ) *
          (∑ k : Fin 7, (2973 / 5000 : ℚ) ^ sevenCostsAt x k *
              threeQuartersPotential
                (nextThreeQuartersState i (sevenCostsAt x k)) (ys k) +
            if threeQuartersHasShrink i x then
              (2973 / 5000 : ℚ) *
                threeQuartersPotential (shrinkThreeQuartersState i) 0
            else 0) := by
      unfold threeQuartersImage
      rw [Finset.sum_congr rfl fun k _ => by rw [hpotEq k]]
      rw [Bool.not_eq_true] at hs
      simp only [hs, Bool.false_eq_true, if_false]
    exact himg ▸ hcert

end CollatzMoonshot.FrontA
