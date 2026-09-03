import Submission.UnitSlopeMultiplicity
import Submission.ThreeUnitSlopeDensity

/-!
# The limiting multiplicity exponent of the unit-slope block budget

An explicit one-parameter family approaches the rational threshold
29599/56223. This is still a fixed threshold strictly below one.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma three_unit_slope_parametric_budget (k : ℕ) :
    threeBlockMainLimit (widePairScale (56223*k)) (106496*k+16) (5950*k) < 1 := by
  apply (threeBlockMainLimit_le_telescoped _ _ _ (by omega)).trans_lt
  have hden : (0 : ℝ) < (((106496*k+16 : ℕ) : ℝ)-2)*
      ((((106496*k+16 : ℕ) : ℝ)+(5950*k : ℕ))-2) := by
    push_cast
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    exact mul_pos (by linarith) (by linarith)
  apply (div_lt_one hden).mpr
  simp only [widePairScale,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- These scale parameters approach smoothness ratio 26624/56223. -/
theorem exists_three_unit_slope_parametric_smooth_count (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (224892*k+20) m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN (224892*k+20) m)
          (independentN (106496*k+21) m)).card : ℝ) := by
  obtain ⟨K,C,hK,hC,H⟩ := widePair_three_unit_slope_smooth_count (56223*k) (106496*k+21)
    (106496*k+16) (5950*k) (by omega) (by omega) (by omega)
    (by unfold widePairScale; omega) (by omega) (by omega) (three_unit_slope_parametric_budget k)
  have ht : widePairScale (56223*k)=224892*k+20 := by unfold widePairScale; ring
  rw [ht] at H
  exact eventual_single_log_count_of_fixed_enlargement _ _ K C (by omega) hC H

/-- Every exponent strictly below 29599/56223 (~0.5264571439) is attained infinitely often. -/
theorem infinite_g_gt_three_unit_slope_limit (γ : ℝ) (hγ : γ < 29599/56223) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  have hgap : 0 < 118396-224892*γ := by linarith only [hγ]
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((1+20*γ)/(118396-224892*γ)))
  have hkR : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk1 : 1 ≤ k := by exact_mod_cast hkR.le
  have hlarge := (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hk)
  obtain ⟨C,hC,H⟩ := exists_three_unit_slope_parametric_smooth_count k hk1
  apply infinite_g_gt_of_single_log_smooth_count (224892*k+20) (106496*k+21) C (by omega) H γ
  have ht : (0 : ℝ) < (224892*k+20 : ℕ) := by positivity
  have hh : ((106496*k+21 : ℕ) : ℝ)/((224892*k+20 : ℕ) : ℝ) < 1-γ := by
    apply (div_lt_iff₀ ht).mpr
    push_cast
    nlinarith only [hlarge]
  linarith only [hh]

theorem erdos_821_three_unit_slope_limit_range (ε : ℝ) (hε : 26624/56223 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_three_unit_slope_limit (1-ε) (by linarith only [hε])

lemma three_unit_slope_improves_previous_limit :
    (14587/27899 : ℝ) < 29599/56223 := by norm_num

theorem infinite_g_gt_point_five_two_six_four_five :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(10529/20000 : ℝ)}.Infinite :=
  infinite_g_gt_three_unit_slope_limit _ (by norm_num)

end Erdos821
