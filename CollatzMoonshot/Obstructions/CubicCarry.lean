import CollatzMoonshot.Obstructions.SignedFlow
import CollatzMoonshot.Obstructions.CubicPeel

/-! Exact carry relations between the hard cubic progression and the orbit of
its first auxiliary label.  These identities concern finite prefixes only. -/

namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

open CollatzMoonshot.FrontB

/-- The even neighbor lying fourteen above the third actual iterate. -/
def neighbor (s : ℕ) : ℕ := 32 * tstep (cubicQ1 s)

/-! ### Local step lemmas

`CubicPeel` keeps its parity facts private, so the parities used below are
re-established here from the affine forms. -/

/-- One accelerated step halves an even number. -/
private theorem tstep_double (u : ℕ) : tstep (2 * u) = u := by
  have h : (2 * u) % 2 = 0 := by omega
  simp only [tstep, h, if_true]
  omega

/-- One accelerated step from an odd number, in the form used for the orbit
table: `v` is pinned by `3*u + 1 = 2*v`. -/
private theorem tstep_odd_val {u v : ℕ} (hu : u % 2 = 1) (h : 3 * u + 1 = 2 * v) :
    tstep u = v := by
  have h2 := two_tstep_odd hu
  omega

private theorem q1_odd (s : ℕ) : cubicQ1 s % 2 = 1 := by
  simp only [cubicQ1]; omega

/-- The auxiliary successor, affinely. -/
private theorem tstep_q1 (s : ℕ) :
    tstep (cubicQ1 s) = 2693975822 + 4116093975 * s :=
  tstep_odd_val (q1_odd s) (by simp only [cubicQ1]; ring)

/-- The neighbor's affine coefficients. -/
private theorem neighbor_eq (s : ℕ) :
    neighbor s = 86207226304 + 131715007200 * s := by
  simp only [neighbor, tstep_q1]; ring

/-! ### The six-term orbit prefix of `cubicN`

All progression slopes before each parity check are even, so each parity is
that of the displayed constant: odd, odd, odd, even, odd, even. -/

private theorem orbit1 (s : ℕ) :
    tstep (cubicN s) = 38314322795 + 58540003200 * s :=
  tstep_odd_val (by simp only [cubicN]; omega) (by simp only [cubicN]; ring)

private theorem orbit2 (s : ℕ) :
    tstep (38314322795 + 58540003200 * s) = 57471484193 + 87810004800 * s :=
  tstep_odd_val (by omega) (by ring)

private theorem orbit3 (s : ℕ) :
    tstep (57471484193 + 87810004800 * s) = 86207226290 + 131715007200 * s :=
  tstep_odd_val (by omega) (by ring)

private theorem orbit4 (s : ℕ) :
    tstep (86207226290 + 131715007200 * s) = 43103613145 + 65857503600 * s := by
  rw [show 86207226290 + 131715007200 * s = 2 * (43103613145 + 65857503600 * s) by ring]
  exact tstep_double _

private theorem orbit5 (s : ℕ) :
    tstep (43103613145 + 65857503600 * s) = 64655419718 + 98786255400 * s :=
  tstep_odd_val (by omega) (by ring)

private theorem orbit6 (s : ℕ) :
    tstep (64655419718 + 98786255400 * s) = 32327709859 + 49393127700 * s := by
  rw [show 64655419718 + 98786255400 * s = 2 * (32327709859 + 49393127700 * s) by ring]
  exact tstep_double _

private theorem iterate_three (s : ℕ) :
    tstep^[3] (cubicN s) = 86207226290 + 131715007200 * s := by
  show tstep (tstep (tstep (cubicN s))) = _
  rw [orbit1, orbit2, orbit3]

private theorem iterate_five (s : ℕ) :
    tstep^[5] (cubicN s) = 64655419718 + 98786255400 * s := by
  show tstep (tstep (tstep (tstep (tstep (cubicN s))))) = _
  rw [orbit1, orbit2, orbit3, orbit4, orbit5]

private theorem iterate_six (s : ℕ) :
    tstep^[6] (cubicN s) = 32327709859 + 49393127700 * s := by
  show tstep (tstep (tstep (tstep (tstep (tstep (cubicN s)))))) = _
  rw [orbit1, orbit2, orbit3, orbit4, orbit5, orbit6]

/-- Two neighbor halvings. -/
private theorem neighbor_two (s : ℕ) :
    tstep^[2] (neighbor s) = 8 * tstep (cubicQ1 s) := by
  show tstep (tstep (neighbor s)) = _
  rw [show neighbor s = 2 * (16 * tstep (cubicQ1 s)) by simp only [neighbor]; ring,
    tstep_double, show 16 * tstep (cubicQ1 s) = 2 * (8 * tstep (cubicQ1 s)) by ring,
    tstep_double]

/-- Five neighbor halvings land on the auxiliary successor. -/
private theorem neighbor_five (s : ℕ) :
    tstep^[5] (neighbor s) = tstep (cubicQ1 s) := by
  show tstep (tstep (tstep (tstep (tstep (neighbor s))))) = _
  set x := tstep (cubicQ1 s) with hx
  rw [show neighbor s = 2 * (16 * x) by simp only [neighbor, hx]; ring, tstep_double,
    show 16 * x = 2 * (8 * x) by ring, tstep_double,
    show 8 * x = 2 * (4 * x) by ring, tstep_double,
    show 4 * x = 2 * (2 * x) by ring, tstep_double, tstep_double]

/-! ### The frozen targets -/

/-- The third actual iterate lies exactly fourteen below the neighbor. -/
theorem cubic_carry_third (s : ℕ) :
    tstep^[3] (cubicN s) + 14 = neighbor s := by
  rw [iterate_three, neighbor_eq]
  omega

/-- After two neighbor halvings, the fifth actual iterate has the indicated
remaining carry from the auxiliary successor. -/
theorem cubic_carry_fifth (s : ℕ) :
    tstep^[5] (cubicN s) + 10 =
      tstep^[2] (neighbor s) + 16 * tstep (cubicQ1 s) := by
  rw [iterate_five, neighbor_two, tstep_q1]
  ring

/-- The simultaneous prefixes have an unbounded gap, even though both vary
affinely with the progression parameter. -/
theorem cubic_carry_gap_unbounded :
    ∀ B : ℕ, ∃ s : ℕ,
      tstep^[2] (neighbor s) + B < tstep^[5] (cubicN s) := by
  intro B
  refine ⟨B, ?_⟩
  rw [iterate_five, neighbor_two, tstep_q1]
  omega

/-- The sixth actual iterate is an affine odd neighbor of the auxiliary
label itself. -/
theorem cubic_carry_sixth (s : ℕ) :
    tstep^[6] (cubicN s) = 18 * cubicQ1 s + 1 := by
  rw [iterate_six]
  simp only [cubicQ1]
  ring

/-- The auxiliary's convergence transfers to its five-halving neighbor. -/
theorem cubic_carry_neighbor_reachesOne (s : ℕ) :
    CollatzMoonshot.Obstructions.SignedFlow.reachesOne (cubicQ1 s) →
      CollatzMoonshot.Obstructions.SignedFlow.reachesOne (neighbor s) := by
  intro h
  obtain ⟨k, hk⟩ :=
    (CollatzMoonshot.Obstructions.SignedFlow.reachesOne_step_iff (cubicQ1 s)).1 h
  exact ⟨k + 5, by rw [Function.iterate_add_apply, neighbor_five]; exact hk⟩

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
