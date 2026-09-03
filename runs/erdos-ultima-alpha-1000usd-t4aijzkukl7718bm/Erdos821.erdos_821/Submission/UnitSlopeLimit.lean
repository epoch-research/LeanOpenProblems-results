import Submission.UnitSlopeMultiplicity

/-!
# The limiting multiplicity exponent of the unit-slope block budget

An explicit one-parameter family approaches the rational threshold
14587/27899. This is still a fixed threshold strictly below one.
-/
open Nat Finset Filter
open scoped Classical BigOperators Topology
namespace Erdos821
open AnalyticSieve HigherDivisors
set_option maxHeartbeats 3000000

lemma unit_slope_parametric_budget (k : ℕ) :
    sharpBlockMainLimit (widePairScale (27899*k)) (53248*k+16) (2550*k) < 1 := by
  apply (sharpBlockMainLimit_le_telescoped _ _ _ (by omega)).trans_lt
  have hden : (0 : ℝ) < (((53248*k+16 : ℕ) : ℝ)-2)*
      ((((53248*k+16 : ℕ) : ℝ)+(2550*k : ℕ))-2) := by
    push_cast
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
    exact mul_pos (by linarith) (by linarith)
  apply (div_lt_one hden).mpr
  simp only [widePairScale,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

/-- These scale parameters approach smoothness ratio 13312/27899. -/
theorem exists_unit_slope_parametric_smooth_count (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℕ, 0 < C ∧ ∀ᶠ m : ℕ in atTop,
      (independentN (111596*k+20) m : ℝ) ≤ (C : ℝ)*m*
        ((smoothPrimePool (independentN (111596*k+20) m)
          (independentN (53248*k+21) m)).card : ℝ) := by
  obtain ⟨K,C,hK,hC,H⟩ := widePair_unit_slope_smooth_count (27899*k) (53248*k+21)
    (53248*k+16) (2550*k) (by omega) (by omega) (by omega)
    (by unfold widePairScale; omega) (by omega) (by omega) (unit_slope_parametric_budget k)
  have ht : widePairScale (27899*k)=111596*k+20 := by unfold widePairScale; ring
  rw [ht] at H
  exact eventual_single_log_count_of_fixed_enlargement _ _ K C (by omega) hC H

/-- Every exponent strictly below 14587/27899 (~0.5228502814) is attained infinitely often. -/
theorem infinite_g_gt_unit_slope_limit (γ : ℝ) (hγ : γ < 14587/27899) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^γ}.Infinite := by
  have hgap : 0 < 58348-111596*γ := by linarith only [hγ]
  obtain ⟨k,hk⟩ := exists_nat_gt (max 1 ((1+20*γ)/(58348-111596*γ)))
  have hkR : (1 : ℝ) < k := (le_max_left _ _).trans_lt hk
  have hk1 : 1 ≤ k := by exact_mod_cast hkR.le
  have hlarge := (div_lt_iff₀ hgap).mp ((le_max_right _ _).trans_lt hk)
  obtain ⟨C,hC,H⟩ := exists_unit_slope_parametric_smooth_count k hk1
  apply infinite_g_gt_of_single_log_smooth_count (111596*k+20) (53248*k+21) C (by omega) H γ
  have ht : (0 : ℝ) < (111596*k+20 : ℕ) := by positivity
  have hh : ((53248*k+21 : ℕ) : ℝ)/((111596*k+20 : ℕ) : ℝ) < 1-γ := by
    apply (div_lt_iff₀ ht).mpr
    push_cast
    nlinarith only [hlarge]
  linarith only [hh]

theorem erdos_821_unit_slope_limit_range (ε : ℝ) (hε : 13312/27899 < ε) :
    {n : ℕ | (g n : ℝ) > (n : ℝ)^(1-ε)}.Infinite :=
  infinite_g_gt_unit_slope_limit (1-ε) (by linarith only [hε])

lemma unit_slope_limit_improves_fixed_parameters :
    (6971337/13333340 : ℝ) < 14587/27899 := by norm_num

end Erdos821
