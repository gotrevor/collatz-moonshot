import CollatzMoonshot.Obstructions.FiveHead

/-! Every individual quadratic exchange has an affine deformation.
This automatic lifting preserves smaller-input inequalities, but supplies
neither borrowing closure nor a terminating repair. -/
namespace CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair

def liftU (u x t : ℕ) : ℕ := u + 3 * u * (3*x+1) * (3*u+1) * t
def liftX (u x t : ℕ) : ℕ := x + 3 * x * (3*x+1) * (3*u+1) * t
def liftZ (u x z t : ℕ) : ℕ := z + 9 * x * z * (3*u+1) * t
def liftB (u x b t : ℕ) : ℕ := b + 9 * u * b * (3*x+1) * t

/-- The common deformation factor `F = 1 + 3(3x+1)(3u+1)t`. -/
private def facF (u x t : ℕ) : ℕ := 1 + 3 * (3*x+1) * (3*u+1) * t
/-- The `b`-side factor `G = 1 + 9u(3x+1)t`. -/
private def facG (u x t : ℕ) : ℕ := 1 + 9 * u * (3*x+1) * t
/-- The `z`-side factor `H = 1 + 9x(3u+1)t`. -/
private def facH (u x t : ℕ) : ℕ := 1 + 9 * x * (3*u+1) * t

private theorem liftU_eq (u x t : ℕ) : liftU u x t = u * facF u x t := by
  simp only [liftU, facF]; ring

private theorem liftX_eq (u x t : ℕ) : liftX u x t = x * facF u x t := by
  simp only [liftX, facF]; ring

private theorem liftZ_eq (u x z t : ℕ) : liftZ u x z t = z * facH u x t := by
  simp only [liftZ, facH]; ring

private theorem liftB_eq (u x b t : ℕ) : liftB u x b t = b * facG u x t := by
  simp only [liftB, facG]; ring

theorem affineLift_preserves_cross (u b x z t : ℕ)
    (hQ : u*b*(3*x+1)*(3*z+1) = x*z*(3*u+1)*(3*b+1)) :
    liftU u x t * liftB u x b t * (3*liftX u x t+1) * (3*liftZ u x z t+1) =
    liftX u x t * liftZ u x z t * (3*liftU u x t+1) * (3*liftB u x b t+1) := by
  have hQ' : (u:ℤ)*b*(3*x+1)*(3*z+1) = (x:ℤ)*z*(3*u+1)*(3*b+1) := by
    exact_mod_cast hQ
  have key : ((liftU u x t * liftB u x b t * (3*liftX u x t+1)
        * (3*liftZ u x z t+1) : ℕ) : ℤ)
      = ((liftX u x t * liftZ u x z t * (3*liftU u x t+1)
        * (3*liftB u x b t+1) : ℕ) : ℤ) := by
    simp only [liftU, liftX, liftZ, liftB]
    push_cast
    linear_combination
      ((1 + 3*(3*(x:ℤ)+1)*(3*(u:ℤ)+1)*t) * (1 + 9*(u:ℤ)*(3*(x:ℤ)+1)*t)
        * (1 + 9*(x:ℤ)*(3*(u:ℤ)+1)*t)) * hQ'
  exact_mod_cast key

theorem affineLift_smaller_inputs (u x z t : ℕ) (hxu : x<u) (hzu : z<u) :
    liftX u x t < liftU u x t ∧ liftZ u x z t < liftU u x t := by
  have hF : 0 < facF u x t := by simp only [facF]; positivity
  have hHF : facH u x t ≤ facF u x t := by
    simp only [facF, facH]; nlinarith [Nat.zero_le (x*(3*u+1)*t), Nat.zero_le t]
  refine ⟨?_, ?_⟩
  · rw [liftX_eq, liftU_eq]
    exact Nat.mul_lt_mul_of_lt_of_le hxu (le_refl _) hF
  · rw [liftZ_eq, liftU_eq]
    calc z * facH u x t ≤ z * facF u x t := Nat.mul_le_mul_left _ hHF
      _ < u * facF u x t := Nat.mul_lt_mul_of_lt_of_le hzu (le_refl _) hF

private theorem mul_domain {m M : ℕ} (hm : 0 < m ∧ m%2=1 ∧ m%3≠0)
    (hM : 0 < M ∧ M%2=1 ∧ M%3=1) : 0 < m*M ∧ (m*M)%2=1 ∧ (m*M)%3≠0 := by
  obtain ⟨hm0, hm2, hm3⟩ := hm
  obtain ⟨hM0, hM2, hM3⟩ := hM
  refine ⟨Nat.mul_pos hm0 hM0, ?_, ?_⟩
  · rw [Nat.mul_mod, hm2, hM2]
  · rw [Nat.mul_mod, hM3, Nat.mul_one]
    omega

/-- All four lifted labels are positive odd 3-free if the original labels are. -/
theorem affineLift_domain (u b x z t : ℕ)
    (hd : ∀ v ∈ [u,b,x,z], 0<v ∧ v%2=1 ∧ v%3≠0) :
    ∀ v ∈ [liftU u x t, liftB u x b t, liftX u x t, liftZ u x z t],
      0<v ∧ v%2=1 ∧ v%3≠0 := by
  have hu := hd u (by simp)
  have hb := hd b (by simp)
  have hx := hd x (by simp)
  have hz := hd z (by simp)
  obtain ⟨k, hk⟩ : ∃ k, x = 2*k+1 := ⟨x/2, by omega⟩
  obtain ⟨j, hj⟩ : ∃ j, u = 2*j+1 := ⟨u/2, by omega⟩
  have hF : 0 < facF u x t ∧ (facF u x t)%2=1 ∧ (facF u x t)%3=1 := by
    have : facF u x t = 1 + 6 * ((3*k+2)*(3*u+1)*t) := by
      simp only [facF, hk]; ring
    rw [this]; omega
  have hG : 0 < facG u x t ∧ (facG u x t)%2=1 ∧ (facG u x t)%3=1 := by
    have : facG u x t = 1 + 6 * (3*u*(3*k+2)*t) := by
      simp only [facG, hk]; ring
    rw [this]; omega
  have hH : 0 < facH u x t ∧ (facH u x t)%2=1 ∧ (facH u x t)%3=1 := by
    have : facH u x t = 1 + 6 * (3*x*(3*j+2)*t) := by
      simp only [facH, hj]; ring
    rw [this]; omega
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h <;> subst h
  · rw [liftU_eq]; exact mul_domain hu hF
  · rw [liftB_eq]; exact mul_domain hb hG
  · rw [liftX_eq]; exact mul_domain hx hF
  · rw [liftZ_eq]; exact mul_domain hz hH

theorem affineLift_unbounded (u x M : ℕ) (hu : 0<u) :
    ∃ t : ℕ, M < liftU u x t := by
  refine ⟨M+1, ?_⟩
  have h1 : 1 ≤ 3 * u * (3*x+1) * (3*u+1) := by
    have : 0 < 3 * u * (3*x+1) * (3*u+1) := by positivity
    omega
  simp only [liftU]
  nlinarith [Nat.zero_le u]

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
