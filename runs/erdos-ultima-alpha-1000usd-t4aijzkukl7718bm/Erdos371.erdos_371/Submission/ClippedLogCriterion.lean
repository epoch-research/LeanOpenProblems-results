import Submission.LogarithmicSignedReduction

/-! An exact arbitrarily-fine continuous-clipping criterion for the conjecture.
No cancellation of the clipped averages is asserted. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

lemma logRatioSet_mono_width (N : ℕ) (δ η : ℝ) (hN : 1 ≤ N) (hδη : δ ≤ η) :
    logRatioSet N δ ⊆ logRatioSet N η := by
  have hp := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1 : ℝ) ≤ N) hδη
  intro n hn
  obtain ⟨hnN,hp1,hp2⟩ := mem_filter.mp hn
  exact mem_filter.mpr ⟨hnN,
    hp1.trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _)),
    hp2.trans (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))⟩

lemma clippedLogSign_small_width_approximation (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ N : ℕ in atTop, ∀ η : ℝ, 0 < η → η ≤ δ →
      (∑ n ∈ range N, |factorSign n-clippedLogSign η N n|)/N ≤ ε := by
  obtain ⟨δ,hδ,hr⟩ := logRatioSet_uniform_rarity (ε/4) (by positivity)
  refine ⟨δ,hδ,?_⟩
  have ht := tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ)
  filter_upwards [hr,ht.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (1 : ℕ)] with N hr ht hN
  intro η hη hηδ
  have hc := (Nat.cast_le (α := ℝ)).mpr (card_le_card (logRatioSet_mono_width N η δ hN.le hηδ))
  have hb := div_le_div_of_nonneg_right ((clippedLogSign_error_sum_bound η hη N hN).trans
    (show 2+2*((logRatioSet N η).card : ℝ) ≤ 2+2*((logRatioSet N δ).card : ℝ) by linarith))
    (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div,mul_div_assoc] at hb
  linarith

lemma clippedLogSign_average_difference_bound (δ : ℝ) (N : ℕ) :
    |(∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, clippedLogSign δ N n)/N| ≤
      (∑ n ∈ range N, |factorSign n-clippedLogSign δ N n|)/N := by
  rw [← sub_div,← sum_sub_distrib,abs_div,abs_of_nonneg (Nat.cast_nonneg (α := ℝ) N)]
  exact div_le_div_of_nonneg_right (abs_sum_le_sum_abs _ _) (Nat.cast_nonneg N)

/-- The density conjecture is equivalent to cancellation of arbitrarily
fine continuous clipped averages. The upper bound on the clipping width is
essential: large widths would make this condition trivially true. -/
theorem density_iff_arbitrarily_fine_clipped_cancellation :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧
        ∀ᶠ N : ℕ in atTop, |(∑ n ∈ range N, clippedLogSign δ N n)/N| ≤ ε := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_count_difference]
  constructor
  · intro h ε hε
    obtain ⟨δ₀,hδ₀,ha⟩ := clippedLogSign_small_width_approximation (ε/2) (by positivity)
    let δ := min δ₀ ε
    have hδ : 0 < δ := lt_min hδ₀ hε
    have hd0 : δ ≤ δ₀ := min_le_left _ _
    have hdε : δ ≤ ε := min_le_right _ _
    refine ⟨δ,hδ,hdε,?_⟩
    have hs := (Metric.tendsto_nhds.mp h) (ε/2) (by positivity)
    filter_upwards [ha,hs] with N ha hs
    rw [Real.dist_eq,sub_zero] at hs
    have he := (clippedLogSign_average_difference_bound δ N).trans (ha δ hδ hd0)
    have ht := abs_sub ((∑ n ∈ range N, clippedLogSign δ N n)/N-(∑ n ∈ range N, factorSign n)/N)
      (-((∑ n ∈ range N, factorSign n)/N))
    simp only [sub_neg_eq_add,sub_add_cancel,abs_neg] at ht
    rw [abs_sub_comm] at he
    linarith
  · intro h
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨δ₀,hδ₀,ha⟩ := clippedLogSign_small_width_approximation (ε/3) (by positivity)
    let e := min (ε/3) δ₀
    have he : 0 < e := lt_min (by positivity) hδ₀
    obtain ⟨δ,hδ,hde,hc⟩ := h e he
    have hd0 : δ ≤ δ₀ := hde.trans (min_le_right _ _)
    have hdε : e ≤ ε/3 := min_le_left _ _
    filter_upwards [ha,hc] with N ha hc
    rw [Real.dist_eq,sub_zero]
    have he' := (clippedLogSign_average_difference_bound δ N).trans (ha δ hδ hd0)
    have ht := abs_sub ((∑ n ∈ range N, factorSign n)/N-(∑ n ∈ range N, clippedLogSign δ N n)/N)
      (-((∑ n ∈ range N, clippedLogSign δ N n)/N))
    simp only [sub_neg_eq_add,sub_add_cancel,abs_neg] at ht
    linarith

#print axioms density_iff_arbitrarily_fine_clipped_cancellation
end Erdos371
