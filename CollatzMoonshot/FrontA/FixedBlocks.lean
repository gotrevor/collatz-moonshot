import CollatzMoonshot.FrontA.BlockLength
import CollatzMoonshot.FrontB.OneCircuit

/-!
# Uniform finiteness for a fixed number of maximal odd runs

Count each maximal true run by its final falling edge, with a false sentinel
after the word. In particular a final odd run is counted even without a
following even step. The word decomposition and all actual head identities
are extracted here; no run decomposition is assumed in the final theorem.
-/

namespace CollatzMoonshot.FrontA

open FrontB
open scoped BigOperators

/-- Number of maximal odd runs in a finite parity word. The false sentinel
counts a terminal true run without introducing an extra Collatz step. -/
def oddRunCount (v : List Bool) : ℕ :=
  (cpairs v false).countP (fun p => p.1 && !p.2)

@[simp] theorem oddRunCount_nil : oddRunCount [] = 0 := rfl

theorem oddRunCount_true (q : ℕ) (hq : 0 < q) :
    oddRunCount (List.replicate q true) = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  exact countP_falls_cpairs_replicate_true k

theorem oddRunCount_head (q e : ℕ) (hq : 0 < q) (he : 0 < e) (v : List Bool) :
    oddRunCount (List.replicate q true ++ List.replicate e false ++ v) =
      1+oddRunCount v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : e ≠ 0)
  simp only [oddRunCount, List.replicate_succ (n := l), List.append_assoc,
    List.cons_append]
  rw [cpairs_append, List.countP_append, countP_falls_cpairs_replicate_true,
    countP_falls_cpairs_false_cons, countP_falls_cpairs_false_prefix]

/-- Extract exactly the maximal odd runs, allowing zero even steps after the
last run. The positivity of every odd length is retained for composition. -/
theorem exists_blockWord_oddRunCount : ∀ v : List Bool, v.head? = some true →
    ∃ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.1) ∧ v = blockWord L ∧
      L.length = oddRunCount v
  | v, hhead => by
    obtain ⟨q, r, hq, hv, hr⟩ := peel_true_run v hhead
    rcases hr with hr | hr
    · subst r
      refine ⟨[(q, 0)], ?_, ?_, ?_⟩
      · simpa using (show 0 < q by omega)
      · simpa [blockWord] using hv
      · rw [hv, List.append_nil, oddRunCount_true q hq]
        rfl
    · obtain ⟨e, s, he, hr2, hs⟩ := peel_false_run r hr
      have hvfull : v = List.replicate q true ++ List.replicate e false ++ s := by
        rw [hv, hr2, List.append_assoc]
      rcases hs with hs | hs
      · subst s
        refine ⟨[(q, e)], ?_, ?_, ?_⟩
        · simpa using (show 0 < q by omega)
        · simpa [blockWord] using hvfull
        · rw [hvfull, oddRunCount_head q e hq he, oddRunCount_nil]
          rfl
      · have hlen : s.length < v.length := by
          rw [hvfull]
          simp only [List.length_append, List.length_replicate]
          omega
        obtain ⟨L, hL, hword, hcount⟩ := exists_blockWord_oddRunCount s hs
        refine ⟨(q,e)::L, ?_, ?_, ?_⟩
        · intro p hp
          rcases List.mem_cons.mp hp with hp | hp
          · subst p; exact hq
          · exact hL p hp
        · rw [hvfull, hword]
          rfl
        · rw [List.length_cons, hcount, hvfull, oddRunCount_head q e hq he]
          omega
  termination_by v => v.length
  decreasing_by exact hlen

private theorem sum_getD_blocks (L : List (ℕ × ℕ)) (f : ℕ × ℕ → ℕ) :
    (∑ i ∈ Finset.range L.length, f (L.getD i (0,0))) = (L.map f).sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, List.map_cons, List.sum_cons, ih]
    omega

/-- Extract every head identity from an actual block word, together with the
correct starting and ending orbit values. -/
theorem blockWord_segment_identities (L : List (ℕ × ℕ)) (n : ℕ)
    (hword : traceWord n (blockWord L).length = blockWord L) :
    ∃ x : ℕ → ℕ, x 0 = n ∧ x L.length = tstep^[(blockWord L).length] n ∧
      ∀ i < L.length,
        2^((L.getD i (0,0)).1+(L.getD i (0,0)).2)*x (i+1)+2^((L.getD i (0,0)).1) =
          3^((L.getD i (0,0)).1)*(x i+1) := by
  induction L generalizing n with
  | nil => exact ⟨fun _ => n, rfl, rfl, by simp⟩
  | cons p L ih =>
    obtain ⟨q,e⟩ := p
    have hlen : (blockWord ((q,e)::L)).length = q+e+(blockWord L).length := by
      simp only [blockWord, List.length_append, List.length_replicate]
    have hsplit : traceWord n (q+e) ++ traceWord (tstep^[q+e] n) (blockWord L).length =
        (List.replicate q true ++ List.replicate e false) ++ blockWord L := by
      rw [← traceWord_add, ← hlen, hword]
      rfl
    obtain ⟨hhead, htail⟩ := List.append_inj hsplit (by simp)
    obtain ⟨y, hy0, hyend, hy⟩ := ih (tstep^[q+e] n) htail
    let x : ℕ → ℕ := fun i => match i with | 0 => n | j+1 => y j
    refine ⟨x, rfl, ?_, ?_⟩
    · change y L.length = _
      rw [hyend, hlen, ← Function.iterate_add_apply]
      congr 1
      omega
    · intro i hi
      cases i with
      | zero =>
        simpa [x, hy0] using segment_identity_of_word hhead
      | succ i =>
        simpa [x] using hy i (by simpa using hi)

/-- The explicit bound is monotone in the permitted number of odd runs. -/
theorem fixedBlockLengthBound_mono : Monotone fixedBlockLengthBound := by
  intro a b hab
  unfold fixedBlockLengthBound
  gcongr <;> norm_num

/-- **Campaign B.** Every odd-start acyclic paradoxical segment with at most
`b` maximal odd runs has length below the explicit `fixedBlockLengthBound b`.
The final run may end odd; no endpoint parity is imposed. -/
theorem acyclicParadoxical_length_lt_of_oddRunCount (n m b : ℕ)
    (hodd : n % 2 = 1) (hap : AcyclicParadoxical n m)
    (hcount : oddRunCount (traceWord n m) ≤ b) :
    m < fixedBlockLengthBound b := by
  have hhead : (traceWord n m).head? = some true := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by have := hap.2.1; omega : m ≠ 0)
    simp [traceWord, hodd]
  obtain ⟨L, hq, hword, hLcount⟩ := exists_blockWord_oddRunCount _ hhead
  have hlen : m = (blockWord L).length := by
    have := congrArg List.length hword
    simpa using this
  have hb : 0 < L.length := by
    by_contra hn
    have : L = [] := List.length_eq_zero_iff.mp (by omega)
    subst L
    simp [blockWord] at hlen
    have := hap.2.1
    omega
  obtain ⟨x, hx0, hxend, hid⟩ := blockWord_segment_identities L n (by rwa [← hlen])
  let q : ℕ → ℕ := fun i => (L.getD i (0,0)).1
  let e : ℕ → ℕ := fun i => (L.getD i (0,0)).2
  have hqpos (i : ℕ) (hi : i < L.length) : 0 < q i := by
    apply hq
    rw [List.getD_eq_getElem L (0,0) hi]
    exact List.getElem_mem hi
  have ha : (∑ i ∈ Finset.range L.length, q i) = ones (traceWord n m) := by
    rw [hword, ones_blockWord]
    exact sum_getD_blocks L Prod.fst
  have hm : (∑ i ∈ Finset.range L.length, (q i+e i)) = m := by
    rw [hlen, length_blockWord]
    exact sum_getD_blocks L (fun p => p.1+p.2)
  have h := headBlock_cascade_length_bound L.length hb q e x hqpos hid
    (by rw [ha, hm]; exact hap.2.2.1)
    (by rw [hx0, hxend, ← hlen]; exact hap.2.2.2)
  rw [hm] at h
  exact h.trans_le (fixedBlockLengthBound_mono (by omega))

/-- Kernel controls for the counting convention, including a terminal odd
run and the established non-vacuity witness at rung three. -/
theorem oddRunCount_boundary_controls :
    oddRunCount [true] = 1 ∧
    oddRunCount [true, true, false, true] = 2 ∧
    oddRunCount (traceWord 7 8) = 3 ∧
    oddRunCount (traceWord 9 8) = 3 ∧
    oddRunCount (traceWord 2305 46) = 13 ∧
    oddRunCount (traceWord 2313 46) = 11 := by
  decide +kernel

/-- The uniform theorem includes the known paradoxical segment 7 to 8. -/
theorem fixedBlockLength_nonvacuous :
    AcyclicParadoxical 7 8 ∧ 8 < fixedBlockLengthBound 3 := by
  refine ⟨acyclicParadoxical_seven_eight, ?_⟩
  exact acyclicParadoxical_length_lt_of_oddRunCount 7 8 3 (by decide)
    acyclicParadoxical_seven_eight (by decide +kernel)

end CollatzMoonshot.FrontA
