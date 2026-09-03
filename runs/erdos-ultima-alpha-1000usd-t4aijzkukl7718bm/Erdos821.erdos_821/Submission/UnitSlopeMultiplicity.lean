import Submission.UnitSlopeWideDensity
import Submission.ParametricWideDensity

/-!
# A fixed multiplicity exponent above 0.52285

A fixed enlargement of the prime cutoff is absorbed by a fixed shift in
scale. This preserves the limiting smoothness ratio. The full conjecture
for arbitrarily small positive epsilon is still not asserted.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma eventual_single_log_count_of_fixed_enlargement (t b K C : ℕ)
    (ht : 1 ≤ t) (hC : 0 < C)
    (H : ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C : ℝ)*((m : ℝ)+1)*
        ((smoothPrimePool (K*independentN t m) (independentN b m)).card : ℝ)) :
    ∃ C' : ℕ, 0 < C' ∧ ∀ᶠ m : ℕ in atTop,
      (independentN t m : ℝ) ≤ (C' : ℝ)*m*
        ((smoothPrimePool (independentN t m) (independentN b m)).card : ℝ) := by
  let s := K+1
  let C' := 2*C*independentN t s
  refine ⟨C',by dsimp [C',independentN]; positivity,?_⟩
  filter_upwards [(tendsto_sub_atTop_nat s).eventually H,eventually_ge_atTop (max 1 s)]
    with M hM hm
  let m := M-s
  have hm1 : 1 ≤ M := (le_max_left _ _).trans hm
  have hMs : s ≤ M := (le_max_right _ _).trans hm
  have heq : m+s=M := Nat.sub_add_cancel hMs
  have hmM : m ≤ M := Nat.sub_le M s
  have hNbound : K*independentN t m ≤ independentN t M := by
    have hh := fixed_multiple_le_shifted_scale t K m ht
    change K*progressionScaleN (t*m) ≤ progressionScaleN (t*(m+s)) at hh
    rw [heq] at hh
    simpa only [independentN,progressionScaleN,mul_assoc] using hh
  have hYbound : independentN b m ≤ independentN b M := by
    unfold independentN
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left _ hmM)
  have hcard : ((smoothPrimePool (K*independentN t m) (independentN b m)).card : ℝ) ≤
      (smoothPrimePool (independentN t M) (independentN b M)).card := by
    apply Nat.cast_le.mpr
    apply card_le_card
    intro p hp
    obtain ⟨hp,hps⟩ := mem_filter.mp hp
    obtain ⟨hpN,hpr⟩ := Nat.mem_primesBelow.mp hp
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by omega,hpr⟩,
      Nat.smoothNumbers_mono hYbound hps⟩
  have hNscale : independentN t M = independentN t m*independentN t s := by
    rw [← heq]
    simp only [independentN,Nat.mul_add,pow_add]
  have hpoly : (m : ℝ)+1 ≤ 2*(M : ℝ) := by
    have h1 : (1 : ℝ) ≤ M := by exact_mod_cast hm1
    have h2 : (m : ℝ) ≤ M := by exact_mod_cast hmM
    linarith
  change (independentN t m : ℝ) ≤ (C : ℝ)*((m : ℝ)+1)*
    ((smoothPrimePool (K*independentN t m) (independentN b m)).card : ℝ) at hM
  calc
    (independentN t M : ℝ) = (independentN t m : ℝ)*(independentN t s : ℝ) := by
      exact_mod_cast hNscale
    _ ≤ ((C : ℝ)*((m : ℝ)+1)*((smoothPrimePool (K*independentN t m)
        (independentN b m)).card : ℝ))*(independentN t s : ℝ) :=
      mul_le_mul_of_nonneg_right hM (Nat.cast_nonneg _)
    _ ≤ ((C : ℝ)*(2*(M : ℝ))*((smoothPrimePool (independentN t M)
        (independentN b M)).card : ℝ))*(independentN t s : ℝ) := by gcongr
    _ = _ := by dsimp [C']; push_cast; ring

/-- The smoothness ratio is 19086009/40000020, with only a single log loss. -/
theorem exists_unit_slope_wide_smooth_prime_count :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN 40000020 m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN 40000020 m) (independentN 19086009 m)).card : ℝ) := by
  have hcoef : sharpBlockMainLimit (widePairScale 10000000) 19086004 914012 < 1 := by
    apply (sharpBlockMainLimit_le_telescoped _ _ _ (by decide)).trans_lt
    norm_num [widePairScale]
  obtain ⟨K,C,hK,hC,H⟩ := widePair_unit_slope_smooth_count 10000000 19086009 19086004 914012
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [widePairScale])
    (by norm_num) (by norm_num) hcoef
  exact eventual_single_log_count_of_fixed_enlargement 40000020 19086009 K C (by decide) hC H

/-- Approximately 0.5228500135749932; this is still a fixed exponent threshold. -/
theorem infinite_g_gt_unit_slope_wide_uniform (γ : ℝ) (hγ : γ < 6971337/13333340) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  obtain ⟨C,hC,H⟩ := exists_unit_slope_wide_smooth_prime_count
  apply infinite_g_gt_of_single_log_smooth_count 40000020 19086009 C (by decide) H γ
  norm_num
  exact hγ

theorem infinite_g_gt_point_five_two_two_eight_five :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(10457/20000 : ℝ)}.Infinite :=
  infinite_g_gt_unit_slope_wide_uniform _ (by norm_num)

theorem erdos_821_unit_slope_wide_range (ε : ℝ) (hε : 6362003/13333340 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_unit_slope_wide_uniform (1-ε) (by linarith only [hε])

lemma unit_slope_threshold_strict_improvement :
    (694837/1333334 : ℝ) < 6971337/13333340 := by norm_num

end Erdos821
