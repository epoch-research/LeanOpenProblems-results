import Submission.LocalFirstMoment

/-! Weighted genuine prime pairs with an arbitrary fixed output ratio cutoff. -/
namespace Erdos972WidePairWeights

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower Erdos972RichSlopes Erdos972Topology

noncomputable def widePairs (A N : ℕ) (α : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ (Ioc 0 N).filter Nat.Prime,
    ∑ q ∈ (Ioc p (A * p)).filter Nat.Prime, pairBox p q α

lemma integrable_widePairs (A N : ℕ) : Integrable (widePairs A N) := by
  classical
  apply integrable_finset_sum
  intro p hp
  exact integrable_finset_sum _ (fun q _ => integrable_pairBox p q)

lemma widePairs_nonneg (A N : ℕ) (α : ℝ) : 0 ≤ widePairs A N α := by
  apply sum_nonneg
  intro p _
  apply sum_nonneg
  intro q _
  apply Set.indicator_nonneg
  intro _ _
  exact mul_nonneg (Real.log_natCast_nonneg p) (Real.log_natCast_nonneg q)

lemma inner_sum_le (A : ℕ) (hA : 1 ≤ A) {α : ℝ} {N p : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime) (hpN : p ≤ N) :
    (∑ q ∈ (Ioc p (A * p)).filter Nat.Prime, pairBox p q α) ≤
      if (⌊α * p⌋₊).Prime then Real.log N * Real.log ((A : ℝ) * N) else 0 := by
  classical
  have hA1R : (1 : ℝ) ≤ A := by exact_mod_cast hA
  let q₀ := ⌊α * p⌋₊
  let s := (Ioc p (A * p)).filter Nat.Prime
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlog8N : 0 ≤ Real.log ((A : ℝ) * N) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
    nlinarith)
  by_cases hmem : q₀ ∈ s
  · have hqp : q₀.Prime := (mem_filter.mp hmem).2
    rw [if_pos hqp]
    change (∑ q ∈ s, pairBox p q α) ≤ _
    rw [sum_eq_single q₀ (fun q _ hq => pairBox_eq_zero_of_ne_floor hp.pos hq)
      (fun h => (h hmem).elim)]
    have hqN : (q₀ : ℝ) ≤ (A : ℝ) * N := by
      have hq : q₀ ≤ A * p := (mem_Ioc.mp (mem_filter.mp hmem).1).2
      exact_mod_cast hq.trans (Nat.mul_le_mul_left A hpN)
    have hlogp : Real.log p ≤ Real.log N :=
      Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpN)
    have hlogq : Real.log q₀ ≤ Real.log ((A : ℝ) * N) :=
      Real.log_le_log (Nat.cast_pos.mpr hqp.pos) hqN
    unfold pairBox
    simp only [Set.indicator]
    split_ifs
    · exact mul_le_mul hlogp hlogq
        (Real.log_nonneg (by exact_mod_cast hqp.one_le)) hlogN
    · exact mul_nonneg hlogN hlog8N
  · have hz : (∑ q ∈ s, pairBox p q α) = 0 := by
      apply sum_eq_zero
      intro q hq
      apply pairBox_eq_zero_of_ne_floor hp.pos
      intro he
      change q = q₀ at he
      exact hmem (he ▸ hq)
    change (∑ q ∈ s, pairBox p q α) ≤ _
    rw [hz]
    split_ifs
    · exact mul_nonneg hlogN hlog8N
    · exact le_rfl

lemma widePairs_le_card (A : ℕ) (hA : 1 ≤ A) {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    widePairs A N α ≤ (pairInputs N α).card * (Real.log N * Real.log ((A : ℝ) * N)) := by
  classical
  unfold widePairs
  calc
    _ ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime,
        if (⌊α * p⌋₊).Prime then Real.log N * Real.log ((A : ℝ) * N) else 0 := by
      apply sum_le_sum
      intro p hp
      exact inner_sum_le A hA hN (mem_filter.mp hp).2 (mem_Ioc.mp (mem_filter.mp hp).1).2
    _ = _ := by simp [pairInputs, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul]

lemma widePairs_le_theta (A : ℕ) (hA : 1 ≤ A) {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    widePairs A N α ≤ Chebyshev.theta N * Real.log ((A : ℝ) * N) := by
  classical
  have hA1R : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hN2 : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hlog8N : 0 ≤ Real.log ((A : ℝ) * N) := Real.log_nonneg (by nlinarith)
  unfold widePairs
  rw [Chebyshev.theta, Nat.floor_natCast, sum_mul]
  apply sum_le_sum
  intro p hp
  obtain ⟨hpN, hp⟩ := mem_filter.mp hp
  have hpp := hp
  have hpN' := (mem_Ioc.mp hpN).2
  have hb := inner_sum_le A hA (α := α) hp.two_le hp (le_refl p)
  by_cases hq : (⌊α * p⌋₊).Prime
  · rw [if_pos hq] at hb
    apply hb.trans
    apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg (by exact_mod_cast hp.one_le))
    apply Real.log_le_log (mul_pos (by exact_mod_cast (show 0 < A by omega)) (Nat.cast_pos.mpr hp.pos))
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hpN') (Nat.cast_nonneg A)
  · rw [if_neg hq] at hb
    exact hb.trans (mul_nonneg (Real.log_nonneg (by exact_mod_cast hp.one_le)) hlog8N)

lemma widePairs_uniform_upper (A : ℕ) (hA : 1 ≤ A) {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    widePairs A N α ≤ Real.log 4 * N * Real.log ((A : ℝ) * N) := by
  have hA1R : (1 : ℝ) ≤ A := by exact_mod_cast hA
  apply (widePairs_le_theta A hA hN α).trans
  apply mul_le_mul_of_nonneg_right (Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg N))
  apply Real.log_nonneg
  have : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  nlinarith

lemma widePairs_mono (A : ℕ) (α : ℝ) : Monotone (fun N => widePairs A N α) := by
  intro N M hNM
  apply sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2.trans hNM⟩, hprime⟩
  · intro p hp _
    have hpp := (mem_filter.mp hp).2
    apply sum_nonneg
    intro q hq
    apply Set.indicator_nonneg
    intro _ _
    exact mul_nonneg (Real.log_nonneg (by exact_mod_cast hpp.one_le))
      (Real.log_nonneg (by exact_mod_cast (mem_filter.mp hq).2.one_le))

lemma widePairs_le_of_not_mem_primeTail (A : ℕ) {α : ℝ} (hα : 0 ≤ α) (hI : Irrational α)
    (N B : ℕ) (hbad : α ∉ primeTail B) : widePairs A N α ≤ widePairs A B α := by
  classical
  by_cases hNB : N ≤ B
  · exact widePairs_mono A α hNB
  have hBN : B ≤ N := by omega
  have heq : widePairs A B α = widePairs A N α := by
    apply sum_subset
    · intro p hp
      obtain ⟨hpI, hprime⟩ := mem_filter.mp hp
      exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp hpI).1, (mem_Ioc.mp hpI).2.trans hBN⟩, hprime⟩
    · intro p hp hpB
      have hpp := (mem_filter.mp hp).2
      have hp0 := (mem_Ioc.mp (mem_filter.mp hp).1).1
      have hBp : B < p := by
        by_contra h
        exact hpB (mem_filter.mpr ⟨mem_Ioc.mpr ⟨hp0, Nat.le_of_not_gt h⟩, hpp⟩)
      apply sum_eq_zero
      intro q hq
      apply pairBox_eq_zero_of_ne_floor hpp.pos
      intro hfloor
      have hqp : (⌊α * p⌋₊).Prime := hfloor ▸ (mem_filter.mp hq).2
      apply hbad
      refine ⟨p, ⌊α * p⌋₊, hBp, hpp, hqp, ?_, Nat.lt_floor_add_one _⟩
      exact lt_of_le_of_ne (Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg p)))
        ((hI.mul_natCast hpp.ne_zero).ne_nat _).symm
  exact heq.ge


#print axioms widePairs_le_card
#print axioms widePairs_uniform_upper
end Erdos972WidePairWeights
