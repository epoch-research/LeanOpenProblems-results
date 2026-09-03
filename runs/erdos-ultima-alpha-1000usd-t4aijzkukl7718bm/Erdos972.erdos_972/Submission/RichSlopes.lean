import Submission.ChebyshevLower

/-!
Arbitrarily many genuine prime pairs at a varying irrational slope.
This does not establish infinitude at any prescribed slope.
-/
namespace Erdos972RichSlopes

open Finset MeasureTheory Filter
open Erdos972ChebyshevLower

noncomputable def pairInputs (N : ℕ) (α : ℝ) : Finset ℕ := by
  classical
  exact (Ioc 0 N).filter fun p => p.Prime ∧ (⌊α * p⌋₊).Prime

lemma pairBox_eq_zero_of_ne_floor {α : ℝ} {p q : ℕ}
    (hp : 0 < p) (hq : q ≠ ⌊α * p⌋₊) : pairBox p q α = 0 := by
  apply Set.indicator_of_notMem
  intro h
  have hpR : (0 : ℝ) < p := Nat.cast_pos.mpr hp
  have hlo := (div_le_iff₀ hpR).mp h.1
  have hhi := (lt_div_iff₀ hpR).mp h.2
  have he : ⌊α * p⌋₊ = q := (Nat.floor_eq_iff (by linarith [Nat.cast_nonneg (α := ℝ) q])).mpr
    ⟨hlo, hhi⟩
  exact hq he.symm

lemma inner_sum_le {α : ℝ} {N p : ℕ} (hN : 2 ≤ N)
    (hp : p.Prime) (hpN : p ≤ N) :
    (∑ q ∈ (Ioc p (8 * p)).filter Nat.Prime, pairBox p q α) ≤
      if (⌊α * p⌋₊).Prime then Real.log N * Real.log (8 * N) else 0 := by
  classical
  let q₀ := ⌊α * p⌋₊
  let s := (Ioc p (8 * p)).filter Nat.Prime
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hlog8N : 0 ≤ Real.log (8 * N) := Real.log_nonneg (by
    have : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
    linarith)
  by_cases hmem : q₀ ∈ s
  · have hqp : q₀.Prime := (mem_filter.mp hmem).2
    rw [if_pos hqp]
    change (∑ q ∈ s, pairBox p q α) ≤ _
    rw [sum_eq_single q₀ (fun q _ hq => pairBox_eq_zero_of_ne_floor hp.pos hq)
      (fun h => (h hmem).elim)]
    have hqN : (q₀ : ℝ) ≤ 8 * N := by
      have hq : q₀ ≤ 8 * p := (mem_Ioc.mp (mem_filter.mp hmem).1).2
      exact_mod_cast hq.trans (Nat.mul_le_mul_left 8 hpN)
    have hlogp : Real.log p ≤ Real.log N :=
      Real.log_le_log (Nat.cast_pos.mpr hp.pos) (Nat.cast_le.mpr hpN)
    have hlogq : Real.log q₀ ≤ Real.log (8 * N) :=
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

lemma weightedPairs_le_card {N : ℕ} (hN : 2 ≤ N) (α : ℝ) :
    weightedPairs N α ≤ (pairInputs N α).card * (Real.log N * Real.log (8 * N)) := by
  classical
  unfold weightedPairs
  calc
    _ ≤ ∑ p ∈ (Ioc 0 N).filter Nat.Prime,
        if (⌊α * p⌋₊).Prime then Real.log N * Real.log (8 * N) else 0 := by
      apply sum_le_sum
      intro p hp
      exact inner_sum_le hN (mem_filter.mp hp).2 (mem_Ioc.mp (mem_filter.mp hp).1).2
    _ = _ := by simp [pairInputs, ← sum_filter, filter_filter, sum_const, nsmul_eq_mul]

lemma ae_irrational : ∀ᵐ α : ℝ, Irrational α := by
  rw [ae_iff]
  simpa only [Irrational, not_not] using
    (Set.countable_range (fun r : ℚ => (r : ℝ))).measure_zero volume

lemma integral_le_of_card_le {N K : ℕ} (hN : 2 ≤ N)
    (hcard : ∀ α : ℝ, 1 < α → α < 9 → Irrational α → (pairInputs N α).card ≤ K) :
    (∫ α : ℝ, weightedPairs N α) ≤ 8 * K * (Real.log N * Real.log (8 * N)) := by
  let C := (K : ℝ) * (Real.log N * Real.log (8 * N))
  have hC : 0 ≤ Real.log N * Real.log (8 * N) := by
    apply mul_nonneg <;> apply Real.log_nonneg
    · exact_mod_cast (by omega : 1 ≤ N)
    · have : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
      linarith
  have hbound : (fun α => weightedPairs N α) ≤ᵐ[volume]
      (Set.Ioo (1 : ℝ) 9).indicator (fun _ => C) := by
    filter_upwards [ae_irrational] with α hI
    by_cases hm : α ∈ Set.Ioo (1 : ℝ) 9
    · rw [Set.indicator_of_mem hm]
      apply (weightedPairs_le_card hN α).trans
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hcard α hm.1 hm.2 hI)) hC
    · rw [weightedPairs_eq_zero_of_not_mem N hm, Set.indicator_of_notMem hm]
  have hi := integral_mono_ae (integrable_weightedPairs N)
    ((integrableOn_const (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ioo) hbound
  rw [integral_indicator_const _ measurableSet_Ioo, Real.volume_real_Ioo] at hi
  norm_num only [show (9 : ℝ) - 1 = 8 by norm_num, max_eq_left (by norm_num : (0 : ℝ) ≤ 8),
    smul_eq_mul] at hi
  dsimp [C] at hi
  nlinarith

lemma eventually_log_product_small (K : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      8 * K * (Real.log N * Real.log (8 * N)) < (Real.log 2 ^ 2 / 2) * N := by
  let c : ℝ := Real.log 2 ^ 2 / 2
  have hc : 0 < c := by dsimp [c]; positivity
  have hε : 0 < c / (64 * ((K : ℝ) + 1)) := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop (s := 1) 2 (by norm_num)).bound hε
  have hoN := tendsto_natCast_atTop_atTop.eventually ho
  filter_upwards [hoN, eventually_ge_atTop (2 : ℕ)] with N hsmall hN
  have hN2 : (2 : ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hpow (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := Real.rpow_natCast x 2
  simp only [hpow, Real.rpow_one, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (Real.log (N : ℝ))),
    abs_of_pos hN0] at hsmall
  have hlog8 : Real.log (8 * N) ≤ 4 * Real.log N := by
    rw [Real.log_mul (by norm_num) hN0.ne']
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    rw [h8]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) hN2]
  have hb : Real.log N * Real.log (8 * N) ≤ 4 * Real.log N ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hlog8 hlogN]
  have hs := (le_div_iff₀ (show (0 : ℝ) < 64 * ((K : ℝ) + 1) by positivity)).mp
    (show Real.log N ^ 2 ≤ c * N / (64 * ((K : ℝ) + 1)) by
      convert hsmall using 1; ring)
  have hn : 0 < c * N := mul_pos hc hN0
  have hm := mul_le_mul_of_nonneg_left hb (show (0 : ℝ) ≤ 8 * K by positivity)
  change _ < c * N
  nlinarith [sq_nonneg (Real.log (N : ℝ)), Nat.cast_nonneg (α := ℝ) K]

/-- There are arbitrarily rich finite prime-pair configurations at irrational slopes
in the fixed interval `(1,9)`. Both the slope and the upper input cutoff may depend
on the requested number of pairs. -/
theorem exists_irrational_many_pairs (K : ℕ) :
    ∃ α : ℝ, 1 < α ∧ α < 9 ∧ Irrational α ∧
      ∃ N : ℕ, K < (pairInputs N α).card := by
  classical
  by_contra h
  push_neg at h
  obtain ⟨N, hN2, hlower, hsmall⟩ :=
    ((eventually_ge_atTop (2 : ℕ)).and
      (eventually_integral_weightedPairs_lower.and (eventually_log_product_small K))).exists
  have hupper := integral_le_of_card_le hN2 (fun α hlo hhi hI => h α hlo hhi hI N)
  linarith

/-- The same finite richness holds with every prime input above an arbitrary
prescribed threshold. The slope is still allowed to vary. -/
theorem exists_many_pairs_beyond (B K : ℕ) :
    ∃ α : ℝ, 1 < α ∧ α < 9 ∧ Irrational α ∧
      ∃ S : Finset ℕ, K < S.card ∧
        ∀ p ∈ S, B < p ∧ p.Prime ∧ (⌊α * p⌋₊).Prime := by
  classical
  obtain ⟨α, hlo, hhi, hI, N, hcount⟩ := exists_irrational_many_pairs (B + K)
  let S := (pairInputs N α).filter (fun p => B < p)
  have hsmall : ((pairInputs N α).filter (fun p => ¬ B < p)).card ≤ B := by
    have hsub : (pairInputs N α).filter (fun p => ¬ B < p) ⊆ Ioc 0 B := by
      intro p hp
      obtain ⟨hp, hB⟩ := mem_filter.mp hp
      have hp0 : 0 < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
      exact mem_Ioc.mpr ⟨hp0, Nat.le_of_not_gt hB⟩
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  have hsum := card_filter_add_card_filter_not (s := pairInputs N α) (fun p => B < p)
  have hK : K < S.card := by dsimp [S]; omega
  refine ⟨α, hlo, hhi, hI, S, hK, ?_⟩
  intro p hp
  obtain ⟨hp, hBp⟩ := mem_filter.mp hp
  exact ⟨hBp, (mem_filter.mp hp).2⟩

#print axioms exists_irrational_many_pairs
#print axioms exists_many_pairs_beyond

end Erdos972RichSlopes
