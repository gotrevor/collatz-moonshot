import CollatzMoonshot.Obstructions.CatalyticRepair

namespace CollatzMoonshot.Obstructions.ArithmeticLifts

/-- A deliberately coarse bound for positive integer labels in a product of
`3 + 1/u` with rational target denominator bounded by `b`. -/
def productLabelBound : ℕ → ℕ → ℕ
  | 0, _ => 0
  | q + 1, b =>
    let m := (q + 1) * 4 ^ (q + 1) * b
    max m (productLabelBound q (b * (3 * m + 1)))

/-! ### Elementary helpers -/

/-- A nonempty list of naturals has a least member. -/
private theorem exists_min_mem (xs : List ℕ) (h : xs ≠ []) :
    ∃ v ∈ xs, ∀ u ∈ xs, v ≤ u := by
  induction xs with
  | nil => exact absurd rfl h
  | cons u ys ih =>
    by_cases hy : ys = []
    · exact ⟨u, by simp, by subst hy; simp⟩
    · obtain ⟨v, hv, hmin⟩ := ih hy
      rcases le_total u v with hle | hle
      · refine ⟨u, by simp, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact le_rfl
        · exact hle.trans (hmin x hx)
      · refine ⟨v, List.mem_cons_of_mem _ hv, ?_⟩
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact hle
        · exact hmin x hx

/-- Each factor `3 * u + 1` strictly beats `3 * u`, so a nonempty product of
positive labels strictly exceeds `3 ^ length` times the label product. -/
private theorem pow_mul_prod_lt (xs : List ℕ) (hpos : ∀ u ∈ xs, 0 < u)
    (hne : xs ≠ []) :
    3 ^ xs.length * xs.prod < (xs.map (fun u => 3 * u + 1)).prod := by
  induction xs with
  | nil => exact absurd rfl hne
  | cons u ys ih =>
    have hu : 0 < u := hpos u (by simp)
    by_cases hy : ys = []
    · subst hy; simp
    · have hys := ih (fun x hx => hpos x (List.mem_cons_of_mem _ hx)) hy
      rw [List.length_cons, List.map_cons, List.prod_cons, List.prod_cons]
      calc 3 ^ (ys.length + 1) * (u * ys.prod)
          = (3 * u) * (3 ^ ys.length * ys.prod) := by ring
        _ < (3 * u) * (ys.map (fun u => 3 * u + 1)).prod :=
              mul_lt_mul_of_pos_left hys (by omega)
        _ ≤ (3 * u + 1) * (ys.map (fun u => 3 * u + 1)).prod :=
              Nat.mul_le_mul_right _ (by omega)

/-- The purely arithmetic core of the telescoping estimate. -/
private theorem excess_step (n u v A C : ℕ) (hu : 0 < u) (hvu : v ≤ u)
    (hAC : A ≤ C) :
    v * A + (3 * u + 1) * (n * C) ≤ 4 * (n + 1) * (u * C) := by
  have h1 : v * A ≤ u * C := Nat.mul_le_mul hvu hAC
  have h2 : (3 * u + 1) * (n * C) ≤ 4 * u * (n * C) :=
    Nat.mul_le_mul_right _ (by omega)
  have h3 : u * C + 4 * u * (n * C) = (4 * n + 1) * (u * C) := by ring
  have h4 : (4 * n + 1) * (u * C) ≤ (4 * n + 4) * (u * C) :=
    Nat.mul_le_mul_right _ (by omega)
  have h5 : (4 * n + 4) * (u * C) = 4 * (n + 1) * (u * C) := by ring
  calc v * A + (3 * u + 1) * (n * C) ≤ u * C + 4 * u * (n * C) :=
        Nat.add_le_add h1 h2
    _ = (4 * n + 1) * (u * C) := h3
    _ ≤ (4 * n + 4) * (u * C) := h4
    _ = 4 * (n + 1) * (u * C) := h5

/-- Telescoping bound: with every label at least `v`, the excess of
`∏ (3 + 1/u)` over `3 ^ length` is at most `length * 4 ^ length / v`.
Stated after clearing denominators, with the loose `4 ^ length`. -/
private theorem prod_excess_le (v : ℕ) (xs : List ℕ)
    (hv : ∀ u ∈ xs, 0 < u ∧ v ≤ u) :
    v * (xs.map (fun u => 3 * u + 1)).prod
      ≤ v * (3 ^ xs.length * xs.prod)
        + xs.length * (4 ^ xs.length * xs.prod) := by
  induction xs with
  | nil => simp
  | cons u ys ih =>
    obtain ⟨hu, hvu⟩ := hv u (by simp)
    have ihy := ih (fun x hx => hv x (List.mem_cons_of_mem _ hx))
    have hAC : 3 ^ ys.length * ys.prod ≤ 4 ^ ys.length * ys.prod :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (by omega) _)
    have hstep := excess_step ys.length u v
      (3 ^ ys.length * ys.prod) (4 ^ ys.length * ys.prod) hu hvu hAC
    rw [List.length_cons, List.map_cons, List.prod_cons, List.prod_cons]
    calc v * ((3 * u + 1) * (ys.map (fun u => 3 * u + 1)).prod)
        = (3 * u + 1) * (v * (ys.map (fun u => 3 * u + 1)).prod) := by ring
      _ ≤ (3 * u + 1) * (v * (3 ^ ys.length * ys.prod)
            + ys.length * (4 ^ ys.length * ys.prod)) :=
          Nat.mul_le_mul_left _ ihy
      _ = (3 * u) * (v * (3 ^ ys.length * ys.prod))
            + (v * (3 ^ ys.length * ys.prod)
              + (3 * u + 1) * (ys.length * (4 ^ ys.length * ys.prod))) := by ring
      _ ≤ (3 * u) * (v * (3 ^ ys.length * ys.prod))
            + 4 * (ys.length + 1) * (u * (4 ^ ys.length * ys.prod)) :=
          Nat.add_le_add_left hstep _
      _ = v * (3 ^ (ys.length + 1) * (u * ys.prod))
            + (ys.length + 1) * (4 ^ (ys.length + 1) * (u * ys.prod)) := by ring

/-! ### The bound -/

private theorem bounded_aux : ∀ (n : ℕ) (xs : List ℕ) (a b B : ℕ),
    xs.length = n → 0 < b → b ≤ B → (∀ u ∈ xs, 0 < u) →
    a * xs.prod = b * (xs.map (fun u => 3 * u + 1)).prod →
    ∀ u ∈ xs, u ≤ productLabelBound n B := by
  intro n
  induction n with
  | zero =>
    intro xs a b B hlen _ _ _ _ u hu
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp at hu
  | succ q ih =>
    intro xs a b B hlen hb hbB hpos heq u hu
    have hne : xs ≠ [] := by
      intro h; rw [h] at hlen; simp at hlen
    obtain ⟨v, hv, hmin⟩ := exists_min_mem xs hne
    set P := xs.prod with hPdef
    set Q := (xs.map (fun u => 3 * u + 1)).prod with hQdef
    have hP : 0 < P := List.prod_pos hpos
    -- `a / b` strictly exceeds `3 ^ (q+1)`, hence `a ≥ b * 3 ^ (q+1) + 1`.
    have hlt : 3 ^ (q + 1) * P < Q := by
      have := pow_mul_prod_lt xs hpos hne
      rwa [hlen] at this
    have ha : b * 3 ^ (q + 1) < a := by
      refine Nat.lt_of_mul_lt_mul_right (a := P) ?_
      calc b * 3 ^ (q + 1) * P = b * (3 ^ (q + 1) * P) := by ring
        _ < b * Q := mul_lt_mul_of_pos_left hlt hb
        _ = a * P := heq.symm
    -- Clearing denominators: `b * Q ≥ b * 3 ^ (q+1) * P + P`.
    have hlow : b * (3 ^ (q + 1) * P) + P ≤ b * Q := by
      calc b * (3 ^ (q + 1) * P) + P = (b * 3 ^ (q + 1) + 1) * P := by ring
        _ ≤ a * P := Nat.mul_le_mul_right _ (by omega)
        _ = b * Q := heq
    -- Telescoping upper bound on the same excess.
    have hup := prod_excess_le v xs (fun x hx => ⟨hpos x hx, hmin x hx⟩)
    rw [hlen] at hup
    -- Combine.
    have hcomb : v * P ≤ b * ((q + 1) * (4 ^ (q + 1) * P)) := by
      have e1 : v * (b * (3 ^ (q + 1) * P)) + v * P ≤ v * (b * Q) :=
        by have := Nat.mul_le_mul_left v hlow; linarith [this]
      have e2 : b * (v * Q) ≤ b * (v * (3 ^ (q + 1) * P)
          + (q + 1) * (4 ^ (q + 1) * P)) := Nat.mul_le_mul_left _ hup
      nlinarith [e1, e2]
    have hvle : v ≤ (q + 1) * 4 ^ (q + 1) * B := by
      have h1 : v * P ≤ ((q + 1) * 4 ^ (q + 1) * b) * P := by
        calc v * P ≤ b * ((q + 1) * (4 ^ (q + 1) * P)) := hcomb
          _ = ((q + 1) * 4 ^ (q + 1) * b) * P := by ring
      have := Nat.le_of_mul_le_mul_right h1 hP
      exact this.trans (Nat.mul_le_mul_left _ hbB)
    set m := (q + 1) * 4 ^ (q + 1) * B with hm
    -- Erase the minimal label and recurse.
    have hperm : xs.Perm (v :: xs.erase v) := List.perm_cons_erase hv
    have hPe : P = v * (xs.erase v).prod := by
      rw [hPdef, hperm.prod_eq, List.prod_cons]
    have hQe : Q = (3 * v + 1) * ((xs.erase v).map (fun u => 3 * u + 1)).prod := by
      rw [hQdef, (hperm.map (fun u => 3 * u + 1)).prod_eq, List.map_cons,
        List.prod_cons]
    have hlen' : (xs.erase v).length = q := by
      rw [List.length_erase_of_mem hv, hlen]
      omega
    have hpos' : ∀ x ∈ xs.erase v, 0 < x := fun x hx =>
      hpos x (List.mem_of_mem_erase hx)
    have heq' : (a * v) * (xs.erase v).prod
        = (b * (3 * v + 1)) * ((xs.erase v).map (fun u => 3 * u + 1)).prod := by
      have := heq
      rw [hPe, hQe] at this
      linarith [this]
    have hb' : 0 < b * (3 * v + 1) := Nat.mul_pos hb (by omega)
    have hbB' : b * (3 * v + 1) ≤ B * (3 * m + 1) :=
      Nat.mul_le_mul hbB (by omega)
    have hrec := ih (xs.erase v) (a * v) (b * (3 * v + 1)) (B * (3 * m + 1))
      hlen' hb' hbB' hpos' heq'
    show u ≤ productLabelBound (q + 1) B
    rw [productLabelBound]
    by_cases huv : u = v
    · subst huv
      exact le_max_of_le_left hvle
    · exact le_max_of_le_right (hrec u ((List.mem_erase_of_ne huv).2 hu))

/-- Fixing the number of factors and bounding the target denominator bounds
every positive integer label.  The target numerator is unrestricted. -/
theorem rational_product_labels_bounded (xs : List ℕ) (a b B : ℕ)
    (hb : 0 < b) (hbB : b ≤ B)
    (hpos : ∀ u ∈ xs, 0 < u)
    (heq : a * xs.prod = b * (xs.map (fun u => 3 * u + 1)).prod) :
    ∀ u ∈ xs, u ≤ productLabelBound xs.length B :=
  bounded_aux xs.length xs a b B rfl hb hbB hpos heq

/-- A positive value-one word with q odd-edge factors has uniformly bounded
labels.  Oddness is unnecessary for this stronger arithmetic statement. -/
theorem unit_labels_bounded (xs : List ℕ) (t : ℕ)
    (hpos : ∀ u ∈ xs, 0 < u)
    (hunit : 2 ^ (t + xs.length) * xs.prod =
      (xs.map (fun u => 3 * u + 1)).prod) :
    ∀ u ∈ xs, u ≤ productLabelBound xs.length 1 := by
  exact rational_product_labels_bounded xs (2 ^ (t + xs.length)) 1 1
    (by decide) (by decide) hpos (by simpa using hunit)

end CollatzMoonshot.Obstructions.ArithmeticLifts
