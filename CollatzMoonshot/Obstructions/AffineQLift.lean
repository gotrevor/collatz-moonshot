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

/-! ### Simultaneity: the exchange equations do not obstruct joint deformation

The deformation is row-local, and its factor `F = 1+3(3x+1)(3u+1)t` depends on
the row's own labels, so one might hope two rows sharing a label are forced into
incompatible `t`-scalings.  They are not.  `liftU_shared_iff` computes the exact
matching condition, and it is a single linear Diophantine equation with an
obvious unbounded solution set. -/

/-- Exactly when two deformations agree on a shared head label `u`.  The head
constraint collapses to one linear equation in `t` and `s`. -/
theorem liftU_shared_iff (u x x' t s : ℕ) (hu : 0 < u) :
    liftU u x t = liftU u x' s ↔ (3*x+1)*t = (3*x'+1)*s := by
  have hu' : (0:ℤ) < (u:ℤ) := by exact_mod_cast hu
  have hc : ((3:ℤ)*u*(3*u+1)) ≠ 0 := by positivity
  constructor
  · intro h
    have hZ : ((liftU u x t : ℕ) : ℤ) = ((liftU u x' s : ℕ) : ℤ) := by exact_mod_cast h
    simp only [liftU] at hZ
    push_cast at hZ
    have : ((3*(x:ℤ)+1)*t) = ((3*(x':ℤ)+1)*s) := by
      apply mul_left_cancel₀ hc
      linear_combination hZ
    exact_mod_cast this
  · intro h
    have hZ : ((3*(x:ℤ)+1)*(t:ℤ)) = ((3*(x':ℤ)+1)*(s:ℤ)) := by exact_mod_cast h
    have : ((liftU u x t : ℕ) : ℤ) = ((liftU u x' s : ℕ) : ℤ) := by
      simp only [liftU]
      push_cast
      linear_combination (3*(u:ℤ)*(3*(u:ℤ)+1)) * hZ
    exact_mod_cast this

/-- Two quadratic exchanges sharing their head label `u` admit a *joint* affine
deformation, agreeing on the shared label, with the common head unbounded.
So the exchange equations alone place no obstruction on simultaneity: the
witness is `t = (3x'+1)m`, `s = (3x+1)m`. -/
theorem affineLift_simultaneous_shared_head
    (u b x z b' x' z' M : ℕ) (hu : 0 < u)
    (hQ1 : u*b*(3*x+1)*(3*z+1) = x*z*(3*u+1)*(3*b+1))
    (hQ2 : u*b'*(3*x'+1)*(3*z'+1) = x'*z'*(3*u+1)*(3*b'+1)) :
    ∃ t s : ℕ, liftU u x t = liftU u x' s ∧ M < liftU u x t ∧
      liftU u x t * liftB u x b t * (3*liftX u x t+1) * (3*liftZ u x z t+1) =
        liftX u x t * liftZ u x z t * (3*liftU u x t+1) * (3*liftB u x b t+1) ∧
      liftU u x' s * liftB u x' b' s * (3*liftX u x' s+1) * (3*liftZ u x' z' s+1) =
        liftX u x' s * liftZ u x' z' s * (3*liftU u x' s+1)
          * (3*liftB u x' b' s+1) := by
  refine ⟨(3*x'+1)*(M+1), (3*x+1)*(M+1), ?_, ?_,
    affineLift_preserves_cross u b x z _ hQ1,
    affineLift_preserves_cross u b' x' z' _ hQ2⟩
  · rw [liftU_shared_iff _ _ _ _ _ hu]; ring
  · have hA : 0 < 3*u*(3*x+1)*(3*u+1) := by positivity
    have hT : M+1 ≤ (3*x'+1)*(M+1) := Nat.le_mul_of_pos_left _ (by omega)
    have : M+1 ≤ 3*u*(3*x+1)*(3*u+1) * ((3*x'+1)*(M+1)) :=
      le_trans hT (Nat.le_mul_of_pos_left _ hA)
    simp only [liftU]
    calc M < u + (M+1) := by omega
      _ ≤ u + 3*u*(3*x+1)*(3*u+1) * ((3*x'+1)*(M+1)) := by omega
      _ = u + 3*u*(3*x+1)*(3*u+1)*((3*x'+1)*(M+1)) := by ring

/-- Exactly when a row's deformation of its smaller input `x` agrees with the
deformation of `x` as the *head* of a second row.  Again one linear equation. -/
theorem liftX_eq_liftU_iff (u x x₂ t s : ℕ) (hx : 0 < x) :
    liftX u x t = liftU x x₂ s ↔ (3*u+1)*t = (3*x₂+1)*s := by
  have hx' : (0:ℤ) < (x:ℤ) := by exact_mod_cast hx
  have hc : ((3:ℤ)*x*(3*x+1)) ≠ 0 := by positivity
  constructor
  · intro h
    have hZ : ((liftX u x t : ℕ) : ℤ) = ((liftU x x₂ s : ℕ) : ℤ) := by exact_mod_cast h
    simp only [liftX, liftU] at hZ
    push_cast at hZ
    have : ((3*(u:ℤ)+1)*t) = ((3*(x₂:ℤ)+1)*s) := by
      apply mul_left_cancel₀ hc
      linear_combination hZ
    exact_mod_cast this
  · intro h
    have hZ : ((3*(u:ℤ)+1)*(t:ℤ)) = ((3*(x₂:ℤ)+1)*(s:ℤ)) := by exact_mod_cast h
    have : ((liftX u x t : ℕ) : ℤ) = ((liftU x x₂ s : ℕ) : ℤ) := by
      simp only [liftX, liftU]
      push_cast
      linear_combination (3*(x:ℤ)*(3*(x:ℤ)+1)) * hZ
    exact_mod_cast this

/-- The *chained* case, which is the shape the smaller-input recursion actually
produces: row one is `(u,b,x,z)` and row two has head `x`.  A joint deformation
still exists, matching on the shared label `x`, with that label unbounded.
Witness: `t = (3x₂+1)m`, `s = (3u+1)m`.

Together with `affineLift_simultaneous_shared_head` this settles the question
the deformation raises: the exchange equations impose only a single linear
condition per shared label, never an incompatibility.  Any genuine obstruction
to recursive repair must therefore come from the borrowing/unit bookkeeping,
not from the quadratic exchanges. -/
theorem affineLift_simultaneous_chained
    (u b x z b₂ x₂ z₂ M : ℕ) (hx : 0 < x)
    (hQ1 : u*b*(3*x+1)*(3*z+1) = x*z*(3*u+1)*(3*b+1))
    (hQ2 : x*b₂*(3*x₂+1)*(3*z₂+1) = x₂*z₂*(3*x+1)*(3*b₂+1)) :
    ∃ t s : ℕ, liftX u x t = liftU x x₂ s ∧ M < liftX u x t ∧
      liftU u x t * liftB u x b t * (3*liftX u x t+1) * (3*liftZ u x z t+1) =
        liftX u x t * liftZ u x z t * (3*liftU u x t+1) * (3*liftB u x b t+1) ∧
      liftU x x₂ s * liftB x x₂ b₂ s * (3*liftX x x₂ s+1) * (3*liftZ x x₂ z₂ s+1) =
        liftX x x₂ s * liftZ x x₂ z₂ s * (3*liftU x x₂ s+1)
          * (3*liftB x x₂ b₂ s+1) := by
  refine ⟨(3*x₂+1)*(M+1), (3*u+1)*(M+1), ?_, ?_,
    affineLift_preserves_cross u b x z _ hQ1,
    affineLift_preserves_cross x b₂ x₂ z₂ _ hQ2⟩
  · rw [liftX_eq_liftU_iff _ _ _ _ _ hx]; ring
  · have hA : 0 < 3*x*(3*x+1)*(3*u+1) := by positivity
    have hT : M+1 ≤ (3*x₂+1)*(M+1) := Nat.le_mul_of_pos_left _ (by omega)
    have : M+1 ≤ 3*x*(3*x+1)*(3*u+1) * ((3*x₂+1)*(M+1)) :=
      le_trans hT (Nat.le_mul_of_pos_left _ hA)
    simp only [liftX]
    calc M < x + (M+1) := by omega
      _ ≤ x + 3*x*(3*x+1)*(3*u+1) * ((3*x₂+1)*(M+1)) := by omega
      _ = x + 3*x*(3*x+1)*(3*u+1)*((3*x₂+1)*(M+1)) := by ring

/-! ### The no-go: the deformation cannot move the data a borrow argument reads

Simultaneity is unobstructed (above), so if the deformation route is to fail it
must fail because the lifted family carries *the same* congruence and divisibility
data as the original.  It does. -/

/-- Every lifted label is a multiple of the label it deforms.  Hence the
deformation never removes a prime from a label's support; it can only scale. -/
theorem affineLift_dvd (u b x z t : ℕ) :
    u ∣ liftU u x t ∧ b ∣ liftB u x b t ∧ x ∣ liftX u x t ∧ z ∣ liftZ u x z t := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [liftU_eq]; exact Dvd.intro _ rfl
  · rw [liftB_eq]; exact Dvd.intro _ rfl
  · rw [liftX_eq]; exact Dvd.intro _ rfl
  · rw [liftZ_eq]; exact Dvd.intro _ rfl

/-- Unconditionally, the deformation fixes every label's class mod `3`. -/
theorem affineLift_mod_three (u b x z t : ℕ) :
    liftU u x t % 3 = u % 3 ∧ liftB u x b t % 3 = b % 3 ∧
    liftX u x t % 3 = x % 3 ∧ liftZ u x z t % 3 = z % 3 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : liftU u x t = u + 3 * (u*(3*x+1)*(3*u+1)*t) := by simp only [liftU]; ring
    omega
  · have h : liftB u x b t = b + 3 * (3*u*b*(3*x+1)*t) := by simp only [liftB]; ring
    omega
  · have h : liftX u x t = x + 3 * (x*(3*x+1)*(3*u+1)*t) := by simp only [liftX]; ring
    omega
  · have h : liftZ u x z t = z + 3 * (3*x*z*(3*u+1)*t) := by simp only [liftZ]; ring
    omega

/-- If the two head labels `u` and `x` are odd, the deformation fixes every
label's class mod `6` — for all four labels and every deformation parameter `t`.

This is the no-go for the deformation route.  A repair argument whose deficit is
a statement about residues mod `2` or mod `3` (borrow counts, the 3-free
condition, parity of a run) reads exactly the data this theorem shows is
invariant, so no choice of `t` can ever change it.  Combined with
`affineLift_simultaneous_shared_head` and `affineLift_simultaneous_chained`,
which show the exchange equations impose no obstruction at all, the deformation
is revealed as too flexible to be obstructed and too rigid to repair. -/
theorem affineLift_mod_six_invariant (u b x z t : ℕ) (hu : u%2=1) (hx : x%2=1) :
    liftU u x t % 6 = u % 6 ∧ liftB u x b t % 6 = b % 6 ∧
    liftX u x t % 6 = x % 6 ∧ liftZ u x z t % 6 = z % 6 := by
  obtain ⟨j, hj⟩ : ∃ j, x = 2*j+1 := ⟨x/2, by omega⟩
  obtain ⟨i, hi⟩ : ∃ i, u = 2*i+1 := ⟨u/2, by omega⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : liftU u x t = u + 6 * (u*(3*j+2)*(3*u+1)*t) := by
      simp only [liftU, hj]; ring
    omega
  · have h : liftB u x b t = b + 6 * (3*u*b*(3*j+2)*t) := by
      simp only [liftB, hj]; ring
    omega
  · have h : liftX u x t = x + 6 * (x*(3*j+2)*(3*u+1)*t) := by
      simp only [liftX, hj]; ring
    omega
  · have h : liftZ u x z t = z + 6 * (3*x*z*(3*i+2)*t) := by
      simp only [liftZ, hi]; ring
    omega

theorem affineLift_unbounded (u x M : ℕ) (hu : 0<u) :
    ∃ t : ℕ, M < liftU u x t := by
  refine ⟨M+1, ?_⟩
  have h1 : 1 ≤ 3 * u * (3*x+1) * (3*u+1) := by
    have : 0 < 3 * u * (3*x+1) * (3*u+1) := by positivity
    omega
  simp only [liftU]
  nlinarith [Nat.zero_le u]

end CollatzMoonshot.Obstructions.ArithmeticLifts.RestrictedRepair
