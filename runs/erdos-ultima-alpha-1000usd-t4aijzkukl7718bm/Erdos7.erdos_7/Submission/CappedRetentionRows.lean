import Submission.CappedFiberMixture

/-! Full capped-retention rows. Unlike the uncapped baseline representation,
these allow arbitrary nonnegative density caps, including c > p. -/
namespace Erdos7CappedRetentionRows
open scoped BigOperators
open Erdos7CappedFiberMixture
set_option maxHeartbeats 1500000

noncomputable def retained (q c K k : ℝ) : ℝ :=
  if k ≤ K then max 0 (min 1 (c*(1-k/q))) else 0

lemma retained_nonneg (q c K k : ℝ) : 0 ≤ retained q c K k := by
  unfold retained
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

lemma retained_le_one (q c K k : ℝ) : retained q c K k ≤ 1 := by
  unfold retained
  split_ifs
  · exact max_le zero_le_one (min_le_left _ _)
  · exact zero_le_one

lemma retained_antitone (q c K : ℝ) (hq : 0 < q) (hc : 0 ≤ c) :
    Antitone (retained q c K) := by
  intro k l hkl
  by_cases hl : l ≤ K
  · simp only [retained, if_pos hl, if_pos (hkl.trans hl)]
    apply max_le_max le_rfl
    apply min_le_min le_rfl
    apply mul_le_mul_of_nonneg_left _ hc
    exact sub_le_sub_left (div_le_div_of_nonneg_right hkl hq.le) _
  · simpa only [retained, if_neg hl] using retained_nonneg q c K k

/-- Feasible exact retention follows from any upper bound on the bad fiber
fraction. No positive lower bound on 1-alpha is assumed. -/
lemma retained_feasible (q c K k α : ℝ) (hc : 0 ≤ c)
    (hα : α ≤ 1) (hk : α ≤ k/q) :
    retained q c K k ≤ c*(1-α) := by
  have hz : 0 ≤ c*(1-α) := mul_nonneg hc (sub_nonneg.mpr hα)
  unfold retained
  split_ifs
  · apply max_le hz
    exact (min_le_right _ _).trans
      (mul_le_mul_of_nonneg_left (sub_le_sub_left hk _) hc)
  · exact hz

/-- Option none is the baseline; some j is the cumulative multiplier j+2. -/
noncomputable def coefficient (h : ℝ) (q : ℕ → ℝ) (R : ℕ) : Option (Fin R) → ℝ
  | none => h-min h (q 0)
  | some j => min h (q j.val)-min h (q (j.val+1))

lemma coefficient_nonneg (h : ℝ) (q : ℕ → ℝ) (R : ℕ)
    (hq : ∀ j, q (j+1) ≤ q j) (d : Option (Fin R)) :
    0 ≤ coefficient h q R d := by
  cases d with
  | none => exact (capped_coefficient_nonneg h q hq).1
  | some j => exact (capped_coefficient_nonneg h q hq).2 j.val

lemma coefficient_mass (h : ℝ) (hh : 0 ≤ h) (q : ℕ → ℝ) (R : ℕ)
    (hqR : q R=0) : (∑ d, coefficient h q R d) = h := by
  rw [Fintype.sum_option]
  simp only [coefficient]
  rw [Fin.sum_univ_eq_sum_range (fun j => min h (q j)-min h (q (j+1))) R]
  exact capped_coefficients_mass h hh q R hqR

lemma coefficient_monotone (q : ℕ → ℝ) (R : ℕ)
    (hq : ∀ j, q (j+1) ≤ q j) (d : Option (Fin R)) :
    Monotone (fun h => coefficient h q R d) := by
  cases d with
  | none => exact baseline_monotone (q 0)
  | some j => exact min_difference_monotone (q j.val) (q (j.val+1)) (hq j.val)

lemma capped_rows_antitone (q c K : ℝ) (hq : 0 < q) (hc : 0 ≤ c)
    (tail : ℕ → ℝ) (R : ℕ) (htail : ∀ j, tail (j+1) ≤ tail j)
    (d : Option (Fin R)) :
    Antitone (fun k => coefficient (retained q c K k) tail R d) := by
  exact (coefficient_monotone tail R htail d).comp_antitone (retained_antitone q c K hq hc)

/-- Every finite set of actual count values admits an antitone enumeration,
clamped beyond its last row, together with an index for every actual state. -/
theorem exists_antitone_rows {Ω : Type} [Fintype Ω] [Nonempty Ω] (k : Ω → ℝ) :
    ∃ (n : ℕ) (κ : ℕ → ℝ) (row : Ω → ℕ),
      Antitone κ ∧ (∀ x, row x < n) ∧ (∀ x, κ (row x) = k x) ∧
      (∀ r, ∃ x, κ r = k x) := by
  classical
  let T : Finset ℝ := Finset.univ.image k
  have hkT (x : Ω) : k x ∈ T := Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  have hcard : 0 < T.card := Finset.card_pos.mpr ⟨k (Classical.choice ‹Nonempty Ω›), hkT _⟩
  let clamp (r : ℕ) : Fin T.card := ⟨min r (T.card-1), by omega⟩
  have hmclamp : Monotone clamp := by
    intro r s hrs
    exact min_le_min_right _ hrs
  let κ (r : ℕ) : ℝ := T.orderEmbOfFin rfl (clamp r).rev
  have hκ : Antitone κ := by
    intro r s hrs
    exact (T.orderEmbOfFin rfl).monotone (Fin.rev_anti (hmclamp hrs))
  have hex (x : Ω) : ∃ r < T.card, κ r = k x := by
    obtain ⟨i, hi⟩ := (T.orderIsoOfFin rfl).surjective (⟨k x, hkT x⟩ : T)
    have hit : T.orderEmbOfFin rfl i = k x := congrArg Subtype.val hi
    have hcl : clamp i.rev.val = i.rev := by
      apply Fin.ext
      change min i.rev.val (T.card-1) = i.rev.val
      exact min_eq_left (by have := i.rev.isLt; omega)
    refine ⟨i.rev.val, i.rev.isLt, ?_⟩
    simp only [κ, hcl, Fin.rev_rev, hit]
  choose row hrow heq using hex
  refine ⟨T.card, κ, row, hκ, hrow, heq, ?_⟩
  intro r
  have hmem : κ r ∈ T := T.orderEmbOfFin_mem rfl _
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hmem
  exact ⟨x, hx.symm⟩

#print axioms exists_antitone_rows
#print axioms retained_feasible
#print axioms capped_rows_antitone
#print axioms coefficient_mass
end Erdos7CappedRetentionRows
