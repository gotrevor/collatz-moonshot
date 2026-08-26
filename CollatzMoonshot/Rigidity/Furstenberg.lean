/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import CollatzMoonshot.Rigidity.Circle

/-!
# Furstenberg's ×p×q topological rigidity (1967), proved

A closed subset of the circle carried into itself by two multiplicatively
independent multiplication maps is finite or everything.  This file proves the
theorem that `Assumed/Furstenberg.lean` had axiomatized (for `p = 2`, `q = 3`),
so the axiom can be discharged.

**Provenance.**  Furstenberg, *Disjointness in ergodic theory, minimal sets, and
a problem in Diophantine approximation* (1967), Theorem IV.1.  The proof here
follows the elementary route of Boshernitzan (*Elementary proof of Furstenberg's
Diophantine result*, Proc. AMS 122 (1994) 67-70) as presented in Manners,
*A solution to the pyjama problem* (arXiv:1305.1514), §4, which we use as the
proof pin (`papers/` holds the PDF and pin note).  Everything is elementary: no
measure theory, no entropy, no disjointness.

**Architecture** (Manners §4):
1. arithmetic: multiplicative independence, irrationality of `log p / log q`;
2. rotation: an irrational rotation has small nonzero ℕ-multiples, and a small
   step walks δ-densely around the circle;
3. the climb (Furstenberg's Lemma IV.1 / Manners' Lemma 4.2): the ⟨p,q⟩-orbit
   of a small positive real is δ-dense mod 1, via density of the additive
   semigroup `{r log p + s log q}` in a tail of the half-line;
4. small-points corollary (Manners' Corollary 4.3): a closed invariant set
   accumulating at `0` is everything; likewise at a torsion point (translate
   trick);
5. the intersection induction (Manners' proof of Theorem 4.1): if the derived
   set is torsion-free, intersect its translates along a δ-dense grid of
   torsion points fixed by a sub-semigroup `⟨p^m, q^m⟩`; each stage is infinite,
   so its difference set is compact, invariant, accumulates at `0`, hence is
   everything, which hands the next stage its witness.

The two multiplication maps are `(p • ·)` and `(q • ·)` (ℕ-scalar action on
`UnitAddCircle`); `Assumed/Furstenberg.lean`'s `circleDouble`/`circleTriple`
agree with `(2 • ·)`/`(3 • ·)` by `two_nsmul`-style lemmas.
-/

namespace CollatzMoonshot
namespace Furstenberg

open Set Filter Topology

/-! ## §1  Multiplicative independence arithmetic -/

/-- Two naturals are multiplicatively independent: no nontrivial power of one
equals a power of the other. -/
def MultIndep (p q : ℕ) : Prop := ∀ a b : ℕ, p ^ a = q ^ b → a = 0 ∧ b = 0

theorem multIndep_two_three : MultIndep 2 3 := by
  intro a b h
  have hb : b = 0 := by
    by_contra hb
    have h3 : (3 : ℕ) ∣ 2 ^ a := h ▸ dvd_pow_self 3 hb
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  subst hb
  simp only [pow_zero] at h
  rcases Nat.pow_eq_one.mp h with h2 | ha
  · omega
  · exact ⟨ha, rfl⟩

theorem MultIndep.pow {p q : ℕ} (h : MultIndep p q) {m : ℕ} (hm : 0 < m) :
    MultIndep (p ^ m) (q ^ m) := by
  intro a b hab
  rw [← pow_mul, ← pow_mul] at hab
  obtain ⟨ha, hb⟩ := h _ _ hab
  exact ⟨(Nat.mul_eq_zero.mp ha).resolve_left (by omega),
    (Nat.mul_eq_zero.mp hb).resolve_left (by omega)⟩

/-- `p^a = 1` forces `a = 0` when `2 ≤ p`. -/
private theorem pow_eq_one_forces {p a : ℕ} (hp : 2 ≤ p) (h : p ^ a = 1) : a = 0 := by
  rcases Nat.pow_eq_one.mp h with h2 | ha
  · omega
  · exact ha

/-- Multiplicative independence forces distinct semigroup elements to be
distinct as naturals: `p^r * q^s` determines `(r, s)`. -/
theorem MultIndep.pow_mul_pow_injective {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : MultIndep p q) {r s r' s' : ℕ}
    (hrs : p ^ r * q ^ s = p ^ r' * q ^ s') : r = r' ∧ s = s' := by
  have key : ∀ {r s r' s' : ℕ}, r ≤ r' → p ^ r * q ^ s = p ^ r' * q ^ s' →
      r = r' ∧ s = s' := by
    intro r s r' s' hr hrs
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hr
    have hp0 : 0 < p ^ r := pow_pos (by omega) r
    rw [pow_add, mul_assoc] at hrs
    have h1 : q ^ s = p ^ c * q ^ s' := Nat.eq_of_mul_eq_mul_left hp0 hrs
    rcases le_total s' s with hs | hs
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hs
      have hq0 : 0 < q ^ s' := pow_pos (by omega) s'
      have h1' : q ^ e * q ^ s' = p ^ c * q ^ s' := by
        rw [← pow_add, add_comm e s']
        exact h1
      have h2 : q ^ e = p ^ c := Nat.eq_of_mul_eq_mul_right hq0 h1'
      obtain ⟨hc, he⟩ := h _ _ h2.symm
      omega
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hs
      have hq0 : 0 < q ^ s := pow_pos (by omega) s
      have h1' : q ^ s * 1 = q ^ s * (p ^ c * q ^ e) := by
        rw [mul_one]
        nth_rewrite 1 [h1]
        ring
      have h2 : 1 = p ^ c * q ^ e := Nat.eq_of_mul_eq_mul_left hq0 h1'
      have hc : c = 0 := pow_eq_one_forces hp (Nat.dvd_one.mp ⟨q ^ e, h2⟩)
      have he : e = 0 := pow_eq_one_forces hq (Nat.dvd_one.mp ⟨p ^ c, by rw [h2]; ring⟩)
      omega
  rcases le_total r r' with hr | hr
  · exact key hr hrs
  · obtain ⟨h1, h2⟩ := key hr hrs.symm
    omega

/-- Multiplicative independence of `p, q ≥ 2` makes `log p / log q` irrational.
This feeds the irrational-rotation machinery. -/
theorem MultIndep.irrational_log_div_log {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q)
    (h : MultIndep p q) : Irrational (Real.log p / Real.log q) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hlq : 0 < Real.log q := Real.log_pos hq1
  rw [irrational_iff_ne_rational]
  rintro a b hb hab
  have hb' : (b : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb
  have hcross : (b : ℝ) * Real.log p = (a : ℝ) * Real.log q := by
    field_simp at hab
    linarith
  have hsign : 0 < (a : ℝ) / (b : ℝ) := hab ▸ div_pos hlp hlq
  -- `a` and `b` share a sign, so their absolute values satisfy the same relation.
  have habs : (b.natAbs : ℝ) * Real.log p = (a.natAbs : ℝ) * Real.log q := by
    rcases lt_or_gt_of_ne hb' with hbneg | hbpos
    · have haneg : (a : ℝ) < 0 := by
        rcases lt_trichotomy (a : ℝ) 0 with h' | h' | h'
        · exact h'
        · rw [h', zero_div] at hsign; exact absurd hsign (lt_irrefl 0)
        · exfalso
          have : (a : ℝ) / b < 0 := div_neg_of_pos_of_neg h' hbneg
          linarith
      have hbz : b < 0 := by exact_mod_cast hbneg
      have haz : a < 0 := by exact_mod_cast haneg
      have h1 : (b.natAbs : ℝ) = -(b : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((b.natAbs : ℤ)) = -b by omega, Int.cast_neg]
      have h2 : (a.natAbs : ℝ) = -(a : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((a.natAbs : ℤ)) = -a by omega, Int.cast_neg]
      rw [h1, h2]; linarith
    · have hapos : 0 < (a : ℝ) := by
        rcases lt_trichotomy (a : ℝ) 0 with h' | h' | h'
        · exfalso
          have : (a : ℝ) / b < 0 := div_neg_of_neg_of_pos h' hbpos
          linarith
        · rw [h', zero_div] at hsign; exact absurd hsign (lt_irrefl 0)
        · exact h'
      have hbz : 0 < b := by exact_mod_cast hbpos
      have haz : 0 < a := by exact_mod_cast hapos
      have h1 : (b.natAbs : ℝ) = (b : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((b.natAbs : ℤ)) = b by omega]
      have h2 : (a.natAbs : ℝ) = (a : ℝ) := by
        rw [← Int.cast_natCast (R := ℝ), show ((a.natAbs : ℤ)) = a by omega]
      rw [h1, h2]; linarith
  have hpow : (p : ℝ) ^ b.natAbs = (q : ℝ) ^ a.natAbs := by
    have hlog : Real.log ((p : ℝ) ^ b.natAbs) = Real.log ((q : ℝ) ^ a.natAbs) := by
      rw [Real.log_pow, Real.log_pow]
      exact_mod_cast habs
    have hppos : (0 : ℝ) < (p : ℝ) ^ b.natAbs := pow_pos (by linarith) _
    have hqpos : (0 : ℝ) < (q : ℝ) ^ a.natAbs := pow_pos (by linarith) _
    exact Real.log_injOn_pos (mem_Ioi.mpr hppos) (mem_Ioi.mpr hqpos) hlog
  have hnat : p ^ b.natAbs = q ^ a.natAbs := by exact_mod_cast hpow
  exact Int.natAbs_ne_zero.mpr hb (h _ _ hnat).1

/-! ## §2  Rotation: small steps and the walk -/

/-- Distance between real coercions to the unit circle is at most the real
distance. -/
theorem dist_coe_le (a b : ℝ) :
    dist (a : UnitAddCircle) (b : UnitAddCircle) ≤ |a - b| := by
  rw [dist_eq_norm]
  have hcast : (a : UnitAddCircle) - (b : UnitAddCircle) = ((a - b : ℝ) : UnitAddCircle) :=
    (QuotientAddGroup.mk_sub _ a b).symm
  rw [hcast, UnitAddCircle.norm_eq]
  simpa using round_le (a - b) 0

/-- Norm of a real coercion is bounded by the real absolute value. -/
theorem norm_coe_le (a : ℝ) : ‖(a : UnitAddCircle)‖ ≤ |a| := by
  simpa using dist_coe_le a 0

/-- An irrational rotation has arbitrarily small nonzero ℕ-multiples. -/
theorem exists_nsmul_norm_small {θ : ℝ} (hθ : Irrational θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ s : ℕ, 0 < s ∧ (s • (θ : UnitAddCircle)) ≠ 0 ∧
      ‖s • (θ : UnitAddCircle)‖ < δ := by
  set τ : ℝ := min δ (1 / 2) with hτdef
  have hτpos : 0 < τ := lt_min hδ (by norm_num)
  have hτδ : τ ≤ δ := min_le_left _ _
  have hτle : τ ≤ 1 / 2 := min_le_right _ _
  have hdense : DenseRange (· • ((θ : ℝ) : UnitAddCircle) : ℤ → UnitAddCircle) := by
    have hirr : Irrational (θ / 1) := by simpa using hθ
    exact AddCircle.denseRange_zsmul_coe_iff.mpr hirr
  set y : UnitAddCircle := ((τ / 2 : ℝ) : UnitAddCircle) with hydef
  have hynorm : ‖y‖ = τ / 2 := by
    rw [hydef, (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
      (by rw [abs_of_pos (by linarith), abs_one]; linarith)]
    exact abs_of_pos (by linarith)
  obtain ⟨w, hwmem, hwdist⟩ := Metric.mem_closure_iff.mp (hdense y) (τ / 4) (by linarith)
  obtain ⟨z, rfl⟩ := hwmem
  set w : UnitAddCircle := z • ((θ : ℝ) : UnitAddCircle) with hwdef
  have hband : |‖w‖ - τ / 2| < τ / 4 := by
    have hd : |‖w‖ - ‖y‖| ≤ ‖w - y‖ := abs_norm_sub_norm_le w y
    have hd' : ‖w - y‖ < τ / 4 := by
      rw [← dist_eq_norm, dist_comm]
      exact hwdist
    rw [hynorm] at hd
    linarith [lt_of_le_of_lt hd hd']
  have h2 : ‖w‖ < δ := by
    have := abs_lt.mp hband
    linarith
  have h3 : 0 < ‖w‖ := by
    have := abs_lt.mp hband
    linarith
  have hwne : w ≠ 0 := fun h0 => by rw [h0, norm_zero] at h3; exact lt_irrefl 0 h3
  have hz : z ≠ 0 := by
    rintro rfl
    exact hwne (zero_zsmul _)
  have hkey : z.natAbs • ((θ : ℝ) : UnitAddCircle) = w ∨
      z.natAbs • ((θ : ℝ) : UnitAddCircle) = -w := by
    rcases Int.natAbs_eq z with hz' | hz'
    · left
      rw [hwdef, ← natCast_zsmul, ← hz']
    · right
      have hww : w = -((z.natAbs : ℤ) • ((θ : ℝ) : UnitAddCircle)) := by
        rw [hwdef, ← neg_zsmul, ← hz']
      rw [hww, neg_neg, natCast_zsmul]
  refine ⟨z.natAbs, Int.natAbs_pos.mpr hz, ?_, ?_⟩
  · rcases hkey with hk | hk <;> rw [hk]
    · exact hwne
    · simpa using hwne
  · rcases hkey with hk | hk <;> rw [hk]
    · exact h2
    · rw [norm_neg]
      exact h2

/-- Integer coercions vanish on the unit circle. -/
theorem intCast_coe_eq_zero (z : ℤ) : (((z : ℝ)) : UnitAddCircle) = 0 := by
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨z, by simp⟩

/-- The fractional part represents the same circle point. -/
theorem coe_fract (x : ℝ) : ((Int.fract x : ℝ) : UnitAddCircle) = (x : UnitAddCircle) := by
  have h : ((Int.fract x : ℝ) : UnitAddCircle) =
      (x : UnitAddCircle) - (((⌊x⌋ : ℝ)) : UnitAddCircle) :=
    QuotientAddGroup.mk_sub _ x (⌊x⌋ : ℝ)
  rw [h, intCast_coe_eq_zero, sub_zero]

/-- Walking upward: the ℕ-multiples of a small positive real step past every
target within one step. -/
theorem walk_up {u : ℝ} (hu0 : 0 < u) {δ : ℝ} (huδ : u < δ) (y : UnitAddCircle) :
    ∃ k : ℕ, dist y (k • ((u : ℝ) : UnitAddCircle)) < δ := by
  obtain ⟨v₀, rfl⟩ := QuotientAddGroup.mk_surjective y
  set v : ℝ := Int.fract v₀ with hvdef
  have hv0 : 0 ≤ v := Int.fract_nonneg v₀
  refine ⟨⌈v / u⌉₊, ?_⟩
  have h1 : v ≤ (⌈v / u⌉₊ : ℝ) * u := by
    calc v = (v / u) * u := (div_mul_cancel₀ v hu0.ne').symm
    _ ≤ (⌈v / u⌉₊ : ℝ) * u := mul_le_mul_of_nonneg_right (Nat.le_ceil (v / u)) hu0.le
  have h2 : (⌈v / u⌉₊ : ℝ) * u < v + u := by
    have h3 : (⌈v / u⌉₊ : ℝ) < v / u + 1 := Nat.ceil_lt_add_one (div_nonneg hv0 hu0.le)
    calc (⌈v / u⌉₊ : ℝ) * u < (v / u + 1) * u := mul_lt_mul_of_pos_right h3 hu0
    _ = v + u := by field_simp
  have hsmul : (⌈v / u⌉₊ : ℕ) • ((u : ℝ) : UnitAddCircle) =
      (((⌈v / u⌉₊ : ℝ) * u : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [hsmul, ← coe_fract v₀, ← hvdef]
  calc dist ((v : ℝ) : UnitAddCircle) (((⌈v / u⌉₊ : ℝ) * u : ℝ) : UnitAddCircle)
      ≤ |v - (⌈v / u⌉₊ : ℝ) * u| := dist_coe_le _ _
    _ < δ := by rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith

/-- The ℕ-multiples of any nonzero circle point of norm `< δ` form a δ-net. -/
theorem walk_dense {t : UnitAddCircle} (ht : t ≠ 0) {δ : ℝ} (hn : ‖t‖ < δ)
    (y : UnitAddCircle) : ∃ k : ℕ, dist y (k • t) < δ := by
  have hδ : 0 < δ := lt_of_le_of_lt (norm_nonneg t) hn
  obtain ⟨u₀, rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← coe_fract u₀] at ht hn ⊢
  set u : ℝ := Int.fract u₀ with hudef
  have hu0 : 0 ≤ u := Int.fract_nonneg u₀
  have hu1 : u < 1 := Int.fract_lt_one u₀
  have hune : u ≠ 0 := by
    rintro h0
    apply ht
    rw [h0]
    norm_num
  rcases le_or_gt u (1 / 2) with hhalf | hhalf
  · -- positive representative: `‖t‖ = u`, walk up.
    have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = u := by
      rw [(AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
        (by rw [abs_of_nonneg hu0, abs_one]; linarith)]
      exact abs_of_nonneg hu0
    rw [hnorm] at hn
    exact walk_up (lt_of_le_of_ne hu0 (Ne.symm hune)) hn y
  · -- negative representative: `t = -coe(1-u)`, walk the mirror.
    set u' : ℝ := 1 - u with hu'def
    have hu'0 : 0 < u' := by simp [hu'def]; linarith
    have hneg : ((u : ℝ) : UnitAddCircle) = -((u' : ℝ) : UnitAddCircle) := by
      have hsum : ((u : ℝ) : UnitAddCircle) + ((u' : ℝ) : UnitAddCircle) = 0 := by
        rw [← QuotientAddGroup.mk_add]
        have : u + u' = (1 : ℝ) := by rw [hu'def]; ring
        rw [this]
        exact intCast_coe_eq_zero 1 |>.symm ▸ (by norm_num [intCast_coe_eq_zero])
      linear_combination (norm := abel_nf) hsum
    have hnorm : ‖((u : ℝ) : UnitAddCircle)‖ = u' := by
      rw [hneg, norm_neg,
        (AddCircle.norm_coe_eq_abs_iff (p := 1) one_ne_zero).mpr
          (by rw [abs_of_nonneg hu'0.le, abs_one, hu'def]; linarith)]
      exact abs_of_nonneg hu'0.le
    rw [hnorm] at hn
    obtain ⟨k, hk⟩ := walk_up hu'0 hn (-y)
    refine ⟨k, ?_⟩
    rw [hneg, smul_neg, ← dist_neg_neg y (-(k • ((u' : ℝ) : UnitAddCircle))), neg_neg]
    exact hk

/-- Finite-index rotation net: some finite prefix of the ℕ-multiples of an
irrational rotation is δ-dense on the circle. -/
theorem exists_rotation_net {θ : ℝ} (hθ : Irrational θ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ y : UnitAddCircle, ∃ s : ℕ, s ≤ N ∧
      dist y (s • ((θ : ℝ) : UnitAddCircle)) < δ := by
  have hpt : ∀ y : UnitAddCircle, ∃ s : ℕ,
      dist y (s • ((θ : ℝ) : UnitAddCircle)) < δ / 2 := by
    intro y
    obtain ⟨s₀, _, hne, hsmall⟩ := exists_nsmul_norm_small hθ (half_pos hδ)
    obtain ⟨k, hk⟩ := walk_dense hne hsmall y
    exact ⟨s₀ * k, by rwa [mul_nsmul]⟩
  choose f hf using hpt
  obtain ⟨F, hFfin, hFcov⟩ := Metric.totallyBounded_iff.mp
    (isCompact_univ (X := UnitAddCircle)).totallyBounded (δ / 2) (half_pos hδ)
  refine ⟨hFfin.toFinset.sup f, fun y => ?_⟩
  have hy : y ∈ ⋃ c ∈ F, Metric.ball c (δ / 2) := hFcov (mem_univ y)
  obtain ⟨c, hcF, hyc⟩ := mem_iUnion₂.mp hy
  refine ⟨f c, Finset.le_sup (hFfin.mem_toFinset.mpr hcF), ?_⟩
  calc dist y (f c • ((θ : ℝ) : UnitAddCircle))
      ≤ dist y c + dist c (f c • ((θ : ℝ) : UnitAddCircle)) := dist_triangle _ _ _
    _ < δ / 2 + δ / 2 := add_lt_add (Metric.mem_ball.mp hyc) (hf c)
    _ = δ := by ring

/-! ## §3  The multiplicative climb -/

/-- Density of the additive semigroup `{r·log p + s·log q}` in a tail of the
half-line (the quantitative heart of non-lacunarity). -/
theorem log_lattice_tail_dense {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, C ≤ x →
      ∃ r s : ℕ, |((r : ℝ) * Real.log p + (s : ℝ) * Real.log q) - x| < ε := by
  have hlq : (0 : ℝ) < Real.log q := Real.log_pos (by exact_mod_cast hq)
  have hlp : (0 : ℝ) < Real.log p := Real.log_pos (by exact_mod_cast hp)
  set θ : ℝ := Real.log p / Real.log q with hθdef
  have hθirr : Irrational θ := h.irrational_log_div_log hp hq
  have hθpos : 0 < θ := div_pos hlp hlq
  set ε' : ℝ := min (ε / (2 * Real.log q)) (1 / 4) with hε'def
  have hε'pos : 0 < ε' := lt_min (by positivity) (by norm_num)
  obtain ⟨N, hN⟩ := exists_rotation_net hθirr hε'pos
  refine ⟨Real.log q * ((N : ℝ) * θ + 2), by positivity, fun x hx => ?_⟩
  set ξ : ℝ := x / Real.log q with hξdef
  have hξlarge : (N : ℝ) * θ + 2 ≤ ξ := by
    rw [hξdef, le_div_iff₀ hlq]
    calc ((N : ℝ) * θ + 2) * Real.log q = Real.log q * ((N : ℝ) * θ + 2) := by ring
    _ ≤ x := hx
  obtain ⟨r, hrN, hrdist⟩ := hN ((ξ : ℝ) : UnitAddCircle)
  -- Extract the integer `j` with `|r·θ + j - ξ| < ε'`.
  have hsmul : (r : ℕ) • ((θ : ℝ) : UnitAddCircle) = (((r : ℝ) * θ : ℝ) : UnitAddCircle) := by
    rw [← AddCircle.coe_nsmul]
    norm_num [nsmul_eq_mul]
  rw [hsmul] at hrdist
  have hdist_norm : ‖((ξ - (r : ℝ) * θ : ℝ) : UnitAddCircle)‖ < ε' := by
    rw [QuotientAddGroup.mk_sub, ← dist_eq_norm]
    exact hrdist
  rw [UnitAddCircle.norm_eq] at hdist_norm
  set j : ℤ := round (ξ - (r : ℝ) * θ) with hjdef
  have hjapprox : |ξ - (r : ℝ) * θ - (j : ℝ)| < ε' := hdist_norm
  have hrθ : (r : ℝ) * θ ≤ (N : ℝ) * θ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hrN) hθpos.le
  have hj1 : (1 : ℝ) ≤ (j : ℝ) := by
    have h1 : ξ - (r : ℝ) * θ ≥ 2 := by linarith
    have h2 := abs_lt.mp hjapprox
    have hε'le : ε' ≤ 1 / 4 := min_le_right _ _
    linarith
  set s : ℕ := j.toNat with hsdef
  have hsj : (s : ℝ) = (j : ℝ) := by
    have : (0 : ℤ) ≤ j := by exact_mod_cast (by linarith : (0 : ℝ) ≤ (j : ℝ))
    exact_mod_cast Int.toNat_of_nonneg this
  refine ⟨r, s, ?_⟩
  have hexpand : (r : ℝ) * Real.log p + (s : ℝ) * Real.log q - x =
      Real.log q * (((r : ℝ) * θ + (j : ℝ)) - ξ) := by
    rw [hsj, hθdef, hξdef]
    field_simp
  rw [hexpand, abs_mul, abs_of_pos hlq]
  have hε'le : ε' ≤ ε / (2 * Real.log q) := min_le_left _ _
  calc Real.log q * |(r : ℝ) * θ + (j : ℝ) - ξ|
      < Real.log q * ε' := by
        apply mul_lt_mul_of_pos_left _ hlq
        rw [show (r : ℝ) * θ + (j : ℝ) - ξ = -(ξ - (r : ℝ) * θ - (j : ℝ)) by ring, abs_neg]
        exact hjapprox
    _ ≤ Real.log q * (ε / (2 * Real.log q)) := mul_le_mul_of_nonneg_left hε'le hlq.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- One-sided exponential Lipschitz bound (true without any order hypothesis). -/
private theorem exp_sub_exp_le (a b : ℝ) :
    Real.exp a - Real.exp b ≤ (a - b) * Real.exp a := by
  have h1 : 1 - Real.exp (b - a) ≤ a - b := by
    have := Real.add_one_le_exp (b - a)
    linarith
  have h2 : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b - a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show a + (b - a) = b by ring]
  rw [h2, mul_comm]
  exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos a).le

/-- The multiplicative climb (Furstenberg's Lemma IV.1 / Manners' Lemma 4.2):
below a threshold `η`, the ⟨p,q⟩-orbit of any positive real `u < η` lands
within `δ` of every point of `[δ, 1]`. -/
theorem climb {p q : ℕ} (hp : 2 ≤ p) (hq : 2 ≤ q) (h : MultIndep p q)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    ∃ η : ℝ, 0 < η ∧ ∀ u : ℝ, 0 < u → u < η →
      ∀ v : ℝ, δ ≤ v → v ≤ 1 →
        ∃ r s : ℕ, |(p : ℝ) ^ r * (q : ℝ) ^ s * u - v| < δ := by
  set ε : ℝ := δ / 2 with hεdef
  have hε : 0 < ε := half_pos hδ
  have hεq : ε ≤ 1 / 4 := by rw [hεdef]; linarith
  obtain ⟨C, hCpos, hC⟩ := log_lattice_tail_dense hp hq h hε
  refine ⟨δ * Real.exp (-C), by positivity, fun u hu0 huη v hvδ hv1 => ?_⟩
  have hv0 : 0 < v := lt_of_lt_of_le hδ hvδ
  set x : ℝ := Real.log v - Real.log u with hxdef
  have hxlarge : C ≤ x := by
    have h1 : Real.log u < Real.log δ + (-C) := by
      calc Real.log u < Real.log (δ * Real.exp (-C)) := Real.log_lt_log hu0 huη
      _ = Real.log δ + (-C) := by rw [Real.log_mul (by positivity) (by positivity),
        Real.log_exp]
    have h2 : Real.log δ ≤ Real.log v := Real.log_le_log hδ hvδ
    rw [hxdef]
    linarith
  obtain ⟨r, s, hrs⟩ := hC x hxlarge
  refine ⟨r, s, ?_⟩
  set a : ℝ := Real.log ((p : ℝ) ^ r * (q : ℝ) ^ s * u) with hadef
  set b : ℝ := Real.log v with hbdef
  have hppos : (0 : ℝ) < (p : ℝ) ^ r := pow_pos (by positivity) r
  have hqpos : (0 : ℝ) < (q : ℝ) ^ s := pow_pos (by positivity) s
  have haval : a = (r : ℝ) * Real.log p + (s : ℝ) * Real.log q + Real.log u := by
    rw [hadef, Real.log_mul (by positivity) hu0.ne', Real.log_mul hppos.ne' hqpos.ne',
      Real.log_pow, Real.log_pow]
  have hab : |a - b| < ε := by
    rw [haval, hbdef, show (r : ℝ) * Real.log p + (s : ℝ) * Real.log q + Real.log u -
      Real.log v = (r : ℝ) * Real.log p + (s : ℝ) * Real.log q - x by rw [hxdef]; ring]
    exact hrs
  -- Values stay below `exp ε ≤ 4/3`, so the exponential is `4/3`-Lipschitz here.
  have hble : b ≤ 0 := by
    rw [hbdef, ← Real.log_one]
    exact Real.log_le_log hv0 hv1
  have hexpb : Real.exp b = v := by rw [hbdef, Real.exp_log hv0]
  have hexpa : Real.exp a = (p : ℝ) ^ r * (q : ℝ) ^ s * u := by
    rw [hadef, Real.exp_log (by positivity)]
  have hmax : Real.exp (max a b) ≤ Real.exp ε := by
    apply Real.exp_le_exp.mpr
    rcases max_cases a b with ⟨hm, _⟩ | ⟨hm, _⟩
    · rw [hm]
      have := abs_lt.mp hab
      linarith
    · rw [hm]
      linarith [hε.le]
  have hexpε : Real.exp ε ≤ 4 / 3 := by
    have h1 := Real.add_one_le_exp (-ε)
    have h2 : (3 / 4 : ℝ) ≤ Real.exp (-ε) := by linarith
    have h3 : Real.exp ε * Real.exp (-ε) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos ε, Real.exp_pos (-ε)]
  have hfinal : |Real.exp a - Real.exp b| ≤ |a - b| * (4 / 3) := by
    rcases le_total b a with hba | hba
    · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hba))]
      calc Real.exp a - Real.exp b ≤ (a - b) * Real.exp a := exp_sub_exp_le a b
      _ ≤ |a - b| * (4 / 3) := by
        apply mul_le_mul (le_abs_self _) _ (Real.exp_pos a).le (abs_nonneg _)
        calc Real.exp a ≤ Real.exp (max a b) := Real.exp_le_exp.mpr (le_max_left a b)
        _ ≤ Real.exp ε := hmax
        _ ≤ 4 / 3 := hexpε
    · rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr hba)), neg_sub]
      calc Real.exp b - Real.exp a ≤ (b - a) * Real.exp b := exp_sub_exp_le b a
      _ ≤ |a - b| * (4 / 3) := by
        apply mul_le_mul _ _ (Real.exp_pos b).le (abs_nonneg _)
        · rw [abs_sub_comm]; exact le_abs_self _
        calc Real.exp b ≤ Real.exp (max a b) := Real.exp_le_exp.mpr (le_max_right a b)
        _ ≤ Real.exp ε := hmax
        _ ≤ 4 / 3 := hexpε
  rw [← hexpa, ← hexpb]
  calc |Real.exp a - Real.exp b| ≤ |a - b| * (4 / 3) := hfinal
  _ < ε * (4 / 3) := by
    apply mul_lt_mul_of_pos_right hab
    norm_num
  _ ≤ δ := by rw [hεdef]; linarith

end Furstenberg
end CollatzMoonshot
