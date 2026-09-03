import Submission.LogNearTieRarity

/-! Density-zero shrinking logarithmic near-ties, and stability of the
comparison-density problem under subpower multiplicative perturbations. -/

namespace Erdos371
open Finset Filter
open FiniteSieve

lemma logRatioEvent_mono_factor {N M n : ℕ} {δ η : ℝ}
    (hpow : (N : ℝ)^δ ≤ (M : ℝ)^η) (h : logRatioEvent N δ n) :
    logRatioEvent M η n := by
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _)),
    h.2.trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))⟩

/-- An exceptional event that eventually requires a near-tie of every
positive logarithmic width has natural density zero. -/
lemma power_near_tie_exception_hasDensity_zero (E : ℕ → Prop)
    (hE : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, E n → logRatioEvent n δ n) :
    {n | E n}.HasDensity 0 := by
  classical
  rw [density_iff_count]
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ,hδ,hrare⟩ := logRatioSet_uniform_rarity (ε/2) (by positivity)
  obtain ⟨K,hK⟩ := eventually_atTop.mp (hE δ hδ)
  have hsmall := tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)
  filter_upwards [hrare,hsmall.eventually_lt_const (by positivity : (0 : ℝ) < ε/2),
    eventually_gt_atTop (0 : ℕ)] with N hN hsmall hN0
  have hsub : (range N).filter E ⊆ range K ∪ logRatioSet N δ := by
    intro n hn
    obtain ⟨hnN,hEn⟩ := mem_filter.mp hn
    by_cases hnK : n < K
    · exact mem_union_left _ (mem_range.mpr hnK)
    · apply mem_union_right
      apply mem_filter.mpr
      refine ⟨hnN,logRatioEvent_mono_factor ?_ (hK n (by omega) hEn)⟩
      exact Real.rpow_le_rpow (Nat.cast_nonneg n)
        (by exact_mod_cast (mem_range.mp hnN).le) hδ.le
  have hc := (Nat.cast_le (α := ℝ)).mpr ((card_le_card hsub).trans (card_union_le _ _))
  simp only [card_range,Nat.cast_add] at hc
  have hd := div_le_div_of_nonneg_right hc (Nat.cast_nonneg (α := ℝ) N)
  rw [add_div] at hd
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (by positivity)]
  linarith

/-- Any width tending to zero can be used in the pointwise logarithmic
near-tie event, and the resulting set has natural density zero. -/
theorem shrinking_logRatioEvent_hasDensity_zero (w : ℕ → ℝ)
    (hw : Tendsto w atTop (nhds 0)) :
    {n | logRatioEvent n (w n) n}.HasDensity 0 := by
  apply power_near_tie_exception_hasDensity_zero
  intro δ hδ
  filter_upwards [hw.eventually_lt_const hδ,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  intro h
  apply logRatioEvent_mono_factor _ h
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hn.le

lemma multiplicative_order_change_implies_comparable (a b c p q : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (ha : 1 ≤ a) (hb : 1 ≤ b) (hac : a ≤ c) (hbc : b ≤ c)
    (hchange : ¬(a*p < b*q ↔ p < q)) : p ≤ c*q ∧ q ≤ c*p := by
  have hc : 1 ≤ c := ha.trans hac
  have hpap : p ≤ a*p := by nlinarith
  have hqbq : q ≤ b*q := by nlinarith
  have hpcp : p ≤ c*p := by nlinarith
  have hqcq : q ≤ c*q := by nlinarith
  have hap : a*p ≤ c*p := mul_le_mul_of_nonneg_right hac hp
  have hbq : b*q ≤ c*q := mul_le_mul_of_nonneg_right hbc hq
  by_contra hn
  apply hchange
  rcases not_and_or.mp hn with h | h
  · constructor <;> intro h' <;> linarith
  · constructor <;> intro h' <;> linarith

/-- Natural comparison densities are invariant under positive integer
multipliers growing more slowly than every positive power. This theorem
does not assert that any of those densities exists. -/
theorem subpower_multiplicative_perturbation_density_iff (a b : ℕ → ℕ)
    (ha : ∀ n, 1 ≤ a n) (hb : ∀ n, 1 ≤ b n)
    (hasub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (a n : ℝ) ≤ (n : ℝ)^δ)
    (hbsub : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop, (b n : ℝ) ≤ (n : ℝ)^δ)
    (d : ℝ) :
    {n | a n * Nat.maxPrimeFac n < b n * Nat.maxPrimeFac (n+1)}.HasDensity d ↔
      {n | Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)}.HasDensity d := by
  classical
  let E (n : ℕ) : Prop := ¬(a n * Nat.maxPrimeFac n < b n * Nat.maxPrimeFac (n+1) ↔
    Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1))
  apply density_iff_of_exception _ _ E
  · intro n hn
    exact not_not.mp hn
  · apply power_near_tie_exception_hasDensity_zero
    intro δ hδ
    filter_upwards [hasub δ hδ,hbsub δ hδ] with n han hbn
    intro hEn
    apply multiplicative_order_change_implies_comparable (a n) (b n) ((n : ℝ)^δ)
      (Nat.maxPrimeFac n) (Nat.maxPrimeFac (n+1)) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (by exact_mod_cast ha n) (by exact_mod_cast hb n) han hbn
    intro hiff
    apply hEn
    exact_mod_cast hiff

#print axioms shrinking_logRatioEvent_hasDensity_zero
#print axioms subpower_multiplicative_perturbation_density_iff
end Erdos371
