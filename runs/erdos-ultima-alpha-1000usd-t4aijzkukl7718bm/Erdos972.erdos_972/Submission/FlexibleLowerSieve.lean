import Submission.CappedLowerSieve
import Submission.SharpReciprocalPrimeCost

/-! A lower sieve retaining an arbitrary positive main-term fraction.
It does not give a prime-output theorem. -/
namespace Erdos972FlexibleLowerSieve

open Finset Filter
open Erdos972SelbergWeights Erdos972PairSieve Erdos972SelbergLowerMain
open Erdos972SelbergLowerTest Erdos972CappedLowerSieve
open Erdos972SharpReciprocalPrimeCost Erdos972SieveMassLower

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Reducing the positive main-term margin requires a correspondingly
smaller error budget. Both losses are retained explicitly. -/
theorem rough_weight_positive_margin (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z v N : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hv : R^3*Z ≤ v) {X E C A : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hA : 0 < A)
    (hX : (N:ℝ)/2 ≤ X)
    (hmain : 1/(A*sieveMass R) ≤ lowerMain R Z)
    (hbudget : E ≤ (N:ℝ)/(8*A*v))
    (hcap : ∀ n ∈ S, (g n).Coprime Z.factorial → majorant R (g n) ≤ C)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    (N:ℝ)/(4*A*C*sieveMass R) ≤
      ∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0 := by
  have hR0 : (0:ℝ) < R := Nat.cast_pos.mpr hR
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hv0 : (0:ℝ) < v := Nat.cast_pos.mpr ((show 0 < R^3*Z by positivity).trans_le hv)
  have hX0 : 0 ≤ X := (by positivity : (0:ℝ) ≤ (N:ℝ)/2).trans hX
  have hmass := rough_weight_lower_cap S a g ha hR hZ hE hcap hrows
  have hmain' : (N:ℝ)/(2*A*sieveMass R) ≤ X*lowerMain R Z := by
    calc
      _ = ((N:ℝ)/2)*(1/(A*sieveMass R)) := by ring
      _ ≤ _ := mul_le_mul hX hmain (by positivity) hX0
  have hbudget' : E*((Z:ℝ)+1)*(R:ℝ)^2 ≤ (N:ℝ)/(4*A*R) := by
    have hvR : (R:ℝ)^3*Z ≤ v := by exact_mod_cast hv
    have hZR : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have htotal := (le_div_iff₀ (show 0 < 8*A*(v:ℝ) by positivity)).mp hbudget
    have hb := mul_le_mul_of_nonneg_left hvR (mul_nonneg hA.le hE)
    apply (le_div_iff₀ (show 0 < 4*A*(R:ℝ) by positivity)).mpr
    have hZb := mul_le_mul_of_nonneg_left (show (Z:ℝ)+1 ≤ 2*Z by linarith only [hZR])
      (show 0 ≤ 4*A*E*(R:ℝ)^3 by positivity)
    nlinarith only [htotal, hb, hZb]
  have hbudgetG : E*((Z:ℝ)+1)*(R:ℝ)^2 ≤ (N:ℝ)/(4*A*sieveMass R) := by
    apply hbudget'.trans
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left (sieveMass_le R) (by positivity : 0 ≤ 4*A))
  have hh : (N:ℝ)/(4*A*sieveMass R) ≤
      C*(∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0) := by
    have he : (N:ℝ)/(2*A*sieveMass R) = 2*((N:ℝ)/(4*A*sieveMass R)) := by ring
    linarith only [hmass, hmain', hbudgetG, he]
  apply (div_le_iff₀ (show 0 < 4*A*C*sieveMass R by positivity)).mpr
  have ht := (div_le_iff₀ (show 0 < 4*A*sieveMass R by positivity)).mp hh
  nlinarith only [ht]

theorem rough_weight_log_lower_margin (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z v N : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hv : R^3*Z ≤ v) {X E C A : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hA : 0 < A)
    (hX : (N:ℝ)/2 ≤ X)
    (hmain : 1/(A*sieveMass R) ≤ lowerMain R Z)
    (hbudget : E ≤ (N:ℝ)/(8*A*v))
    (hcap : ∀ n ∈ S, (g n).Coprime Z.factorial → majorant R (g n) ≤ C)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    (N:ℝ)/(12*A*C*(1+Real.log (R+1:ℕ))) ≤
      ∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0 := by
  apply le_trans _ (rough_weight_positive_margin S a g ha hR hZ hv hE hC hA hX hmain hbudget hcap hrows)
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  have hh := mul_le_mul_of_nonneg_left (sieveMass_log_upper R)
    (show 0 ≤ 4*A*C by positivity)
  nlinarith only [hh]

/-- The existing local-cost estimate needs only an eighth power if the
retained positive fraction is one sixteenth rather than one half. -/
theorem eventually_lowerMain_eight :
    ∀ᶠ Z : ℕ in atTop, 1/(16*sieveMass (Z^8)) ≤ lowerMain (Z^8) Z := by
  filter_upwards [eventually_primeCost_upper, eventually_ge_atTop (1:ℕ)] with Z hcost hZ
  have hR : 1 ≤ Z^8 := one_le_pow₀ hZ
  have hG : 0 < sieveMass (Z^8) := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hmass := log_le_two_sieveMass (Z^8)
  have hlog : 8*Real.log Z ≤ Real.log ((Z^8:ℕ)+1) := by
    have hZ0 : (0:ℝ) < Z := Nat.cast_pos.mpr hZ
    calc
      _ = Real.log (Z^8:ℕ) := by rw [Nat.cast_pow, Real.log_pow]; norm_num
      _ ≤ _ := Real.log_le_log (by positivity) (by linarith)
  have hlarge : 48*primeCost Z ≤ 15*sieveMass (Z^8) := by
    nlinarith only [hmass, hlog, hcost]
  have hsum := localMain_sum_cost hR Z
  have hcost' : 3*primeCost Z/(sieveMass (Z^8))^2 ≤ 15/(16*sieveMass (Z^8)) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hG) (by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hlarge hG.le
    nlinarith only [hh]
  unfold lowerMain
  have he : 1/sieveMass (Z^8) = 15/(16*sieveMass (Z^8)) + 1/(16*sieveMass (Z^8)) := by ring
  linarith only [hsum, hcost', he]

#print axioms rough_weight_log_lower_margin
#print axioms eventually_lowerMain_eight

end Erdos972FlexibleLowerSieve
