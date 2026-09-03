import Submission.QuadraticTranslateScaleExplore
import Submission.PrefixCopyExplore

/-! Every logarithmic-limit witness needs more than any fixed linear number
of points between q^2 and 2q^2, for all sufficiently large q. -/
namespace Erdos66SquareAnnulusMass
open Erdos66Counting Erdos66QuadraticTranslateScale Erdos66PrefixCopy
open Filter AdditiveCombinatorics
open scoped Topology
set_option maxHeartbeats 1800000

lemma square_atTop : Tendsto (fun q : ℕ ↦ q^2) atTop atTop := by
  apply tendsto_atTop_mono _ tendsto_id
  intro q
  change q≤q^2
  rcases Nat.eq_zero_or_pos q with rfl|hq
  · simp
  · nlinarith

lemma linear_div_square_count_zero {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) :
    Tendsto (fun q : ℕ ↦ (q:ℝ)/(count A (q^2):ℝ)) atTop (𝓝 0) := by
  have hh := (sqrt_cutoff_div_count_limit hc ht).comp square_atTop
  change Tendsto (fun q : ℕ ↦ Real.sqrt ((q^2:ℕ):ℝ)/(count A (q^2):ℝ)) atTop (𝓝 0) at hh
  simpa only [Nat.cast_pow,Real.sqrt_sq (Nat.cast_nonneg _)] using hh

/-- This is a necessary condition on EVERY witness, not a contradiction. -/
theorem witness_square_annulus_gt_linear {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) (C : ℝ) :
    ∀ᶠ q : ℕ in atTop,
      (count A (q^2):ℝ)+C*q+C < count A (2*q^2) := by
  have hroot : (5/4:ℝ)<Real.sqrt 2 := by
    have hh := Real.sq_sqrt (show (0:ℝ)≤2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2:ℝ)]
  have hrat := ((count_multiple_ratio hc ht 2 (by norm_num)).comp square_atTop).eventually_const_lt hroot
  have hs := (linear_div_square_count_zero hc ht).const_mul (2*(|C|+1))
  simp only [mul_zero] at hs
  have hsmall := hs.eventually_lt_const (show (0:ℝ)<1/4 by norm_num)
  have hpos := square_atTop.eventually (count_pos_eventually hc ht)
  filter_upwards [hrat,hsmall,hpos,eventually_ge_atTop 1] with q hrat hsmall hpos hq
  have hp : (0:ℝ)<count A (q^2) := by exact_mod_cast hpos
  have hq' : (1:ℝ)≤q := by exact_mod_cast hq
  have hrat' := (lt_div_iff₀ hp).mp hrat
  have hsmall' : 2*(|C|+1)*(q:ℝ)<(1/4:ℝ)*count A (q^2) := by
    apply (div_lt_iff₀ hp).mp
    simpa only [mul_div_assoc] using hsmall
  have hcabs := le_abs_self C
  have hpabs := abs_nonneg C
  have hmul := mul_le_mul_of_nonneg_right hcabs (show (0:ℝ)≤q by positivity)
  have hqmul := mul_le_mul_of_nonneg_left hq' hpabs
  nlinarith only [hrat',hsmall',hcabs,hpabs,hmul,hqmul,hq']

/-- Any bound of the form `2m+4` on the next square window requires
m/q to exceed every fixed constant along witness scales. -/
theorem witness_eventually_large_window_budget {A : Set ℕ} {c : ℝ} (hc : c≠0)
    (ht : Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c)) (C : ℕ) :
    ∀ᶠ q : ℕ in atTop, ∀ m : ℕ,
      count A (2*q^2)≤count A (q^2)+2*m+4 → C*q < m := by
  filter_upwards [witness_square_annulus_gt_linear hc ht ((2*C+4:ℕ):ℝ)] with q hq
  intro m hm
  have hq' : count A (q^2)+(2*C+4)*q+(2*C+4)<count A (2*q^2) := by
    exact_mod_cast hq
  nlinarith

/-- Infinitely late thin doubling windows exclude a logarithmic limit.
The thin-window property is an additional hypothesis on A. -/
theorem no_log_limit_of_frequent_thin_square_annuli (A : Set ℕ) (C : ℕ)
    (hthin : ∀ L : ℕ, ∃ q≥L, count A (2*q^2)≤count A (q^2)+C*q+C)
    (c : ℝ) (hc : c≠0) :
    ¬ Tendsto (fun n ↦ (sumRep A n:ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  obtain ⟨L,hL⟩ := eventually_atTop.mp (witness_square_annulus_gt_linear hc ht (C:ℝ))
  obtain ⟨q,hq,hthin⟩ := hthin L
  have hl := hL q hq
  have hu : (count A (2*q^2):ℝ)≤count A (q^2)+(C:ℝ)*q+C := by exact_mod_cast hthin
  linarith

end Erdos66SquareAnnulusMass
