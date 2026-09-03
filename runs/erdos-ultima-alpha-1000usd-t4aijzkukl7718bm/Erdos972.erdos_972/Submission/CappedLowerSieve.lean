import Submission.SelbergMajorantSize
import Submission.SelbergLowerTest

/-! A lower sieve with the true squared coefficient budget and a separate
pointwise cap on rough outputs. The cap need not grow with the sieve level. -/
namespace Erdos972CappedLowerSieve

open Finset ArithmeticFunction
open Erdos972SelbergWeights Erdos972PairSieve Erdos972SelbergLocalCost
open Erdos972SelbergLowerMain Erdos972SelbergLowerTest Erdos972SelbergMajorantSize
open Erdos972SieveMassInterval

set_option maxHeartbeats 1500000

lemma moment_error_square (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    {R p : ℕ} (hR : 1 ≤ R) {X E : ℝ} (hE : 0 ≤ E)
    (hrows : ∀ z ∈ weightIndices R,
      |row S a g ((weightDivisor z).lcm p)-X/((weightDivisor z).lcm p)| ≤ E) :
    |moment S a g R p-X*localMain R p| ≤ E*(R:ℝ)^2 := by
  rw [moment_expansion, localMain_indices, mul_sum, ← sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ = ∑ z ∈ weightIndices R, |weightCoeff R z| *
      |row S a g ((weightDivisor z).lcm p)-X/((weightDivisor z).lcm p)| := by
      apply sum_congr rfl
      intro z hz
      rw [← abs_mul]
      congr 1
      ring
    _ ≤ ∑ z ∈ weightIndices R, |weightCoeff R z| * E :=
      sum_le_sum (fun z hz => mul_le_mul_of_nonneg_left (hrows z hz) (abs_nonneg _))
    _ = E*(∑ z ∈ weightIndices R, |weightCoeff R z|) := by rw [← sum_mul, mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (weightCoeff_abs_sum_square hR) hE

theorem rough_weight_lower_cap (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    {X E C : ℝ} (hE : 0 ≤ E)
    (hcap : ∀ n ∈ S, (g n).Coprime Z.factorial → majorant R (g n) ≤ C)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    X*lowerMain R Z-E*((Z:ℝ)+1)*(R:ℝ)^2 ≤
      C*(∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0) := by
  have herror {p : ℕ} (hp : 0 < p) (hpZ : p ≤ Z) :
      |moment S a g R p-X*localMain R p| ≤ E*(R:ℝ)^2 := by
    apply moment_error_square S a g hR hE
    intro z hz
    obtain ⟨hd0, hdR⟩ := weightDivisor_bounds hz
    apply hrows _ (Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd0.ne' hp.ne'))
    exact (Nat.lcm_le_mul hd0 hp).trans (Nat.mul_le_mul hdR hpZ)
  have h₁ := (abs_le.mp (herror (p := 1) (by norm_num) hZ)).1
  have hp (p : ℕ) (hp : p ∈ smallPrimes Z) :=
    (abs_le.mp (herror (mem_Ioc.mp (mem_filter.mp hp).1).1 (mem_Ioc.mp (mem_filter.mp hp).1).2)).2
  have hsum : (∑ p ∈ smallPrimes Z, (moment S a g R p-X*localMain R p)) ≤
      (Z:ℝ)*E*(R:ℝ)^2 := by
    apply (sum_le_sum hp).trans
    rw [sum_const, nsmul_eq_mul]
    have hh := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (smallPrimes_card_le Z))
      (show 0 ≤ E*(R:ℝ)^2 by positivity)
    nlinarith only [hh]
  have hlow : X*lowerMain R Z-E*((Z:ℝ)+1)*(R:ℝ)^2 ≤
      ∑ n ∈ S, a n*lowerTest R Z (g n) := by
    rw [lowerTest_sum]
    rw [localMain_one hR] at h₁
    simp only [sum_sub_distrib, ← mul_sum] at hsum
    unfold lowerMain
    nlinarith only [h₁, hsum]
  apply hlow.trans
  rw [mul_sum]
  apply sum_le_sum
  intro n hn
  have hc : lowerTest R Z (g n) ≤ if (g n).Coprime Z.factorial then C else 0 := by
    by_cases hnC : (g n).Coprime Z.factorial
    · rw [if_pos hnC, lowerTest]
      exact (mul_le_of_le_one_left (majorant_nonneg R (g n))
        (by linarith only [smallPrimeCount_nonneg Z (g n)])).trans (hcap n hn hnC)
    · have hh := lowerTest_upper hR Z (g n)
      simpa only [if_neg hnC] using hh
  have hh := mul_le_mul_of_nonneg_left hc (ha n hn)
  split_ifs at hh ⊢ <;> simpa only [mul_zero, mul_comm] using hh

theorem rough_weight_positive_cap (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z v N : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hv : R^3*Z ≤ v) {X E C : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hX : (N:ℝ)/2 ≤ X)
    (hmain : 1/(2*sieveMass R) ≤ lowerMain R Z)
    (hbudget : E ≤ (N:ℝ)/(16*v))
    (hcap : ∀ n ∈ S, (g n).Coprime Z.factorial → majorant R (g n) ≤ C)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    (N:ℝ)/(8*C*sieveMass R) ≤
      ∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0 := by
  have hR0 : (0:ℝ) < R := Nat.cast_pos.mpr hR
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  have hv0 : (0:ℝ) < v := Nat.cast_pos.mpr ((show 0 < R^3*Z by positivity).trans_le hv)
  have hX0 : 0 ≤ X := (by positivity : (0:ℝ) ≤ (N:ℝ)/2).trans hX
  have hmass := rough_weight_lower_cap S a g ha hR hZ hE hcap hrows
  have hmain' : (N:ℝ)/(4*sieveMass R) ≤ X*lowerMain R Z := by
    calc
      _ = ((N:ℝ)/2)*(1/(2*sieveMass R)) := by ring
      _ ≤ _ := mul_le_mul hX hmain (by positivity) hX0
  have hbudget' : E*((Z:ℝ)+1)*(R:ℝ)^2 ≤ (N:ℝ)/(8*R) := by
    have hvR : (R:ℝ)^3*Z ≤ v := by exact_mod_cast hv
    have hZR : (1:ℝ) ≤ Z := by exact_mod_cast hZ
    have htotal := (le_div_iff₀ (show 0 < 16*(v:ℝ) by positivity)).mp hbudget
    have hb := mul_le_mul_of_nonneg_left hvR hE
    apply (le_div_iff₀ (show 0 < 8*(R:ℝ) by positivity)).mpr
    have hZb := mul_le_mul_of_nonneg_left (show (Z:ℝ)+1 ≤ 2*Z by linarith only [hZR])
      (show 0 ≤ 8*E*(R:ℝ)^3 by positivity)
    nlinarith only [htotal, hb, hZb]
  have hbudgetG : E*((Z:ℝ)+1)*(R:ℝ)^2 ≤ (N:ℝ)/(8*sieveMass R) := by
    apply hbudget'.trans
    exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left (sieveMass_le R) (by norm_num))
  have hh : (N:ℝ)/(8*sieveMass R) ≤
      C*(∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0) := by
    have he : (N:ℝ)/(4*sieveMass R) = 2*((N:ℝ)/(8*sieveMass R)) := by ring
    linarith only [hmass, hmain', hbudgetG, he]
  apply (div_le_iff₀ (show 0 < 8*C*sieveMass R by positivity)).mpr
  have ht := (div_le_iff₀ (show 0 < 8*sieveMass R by positivity)).mp hh
  nlinarith only [ht]

lemma sieveMass_log_upper (R : ℕ) : sieveMass R ≤ 3*(1+Real.log (R+1:ℕ)) := by
  have hh := sieveAtom_Ioc_bound (R := R) (p := R+1) (by omega)
  simpa only [Nat.div_eq_of_lt (Nat.lt_succ_self R), sieveMass, sieveAtom] using hh

/-- Retaining the logarithmic normalization removes the old power-of-R
loss in the positive lower bound. -/
theorem rough_weight_log_lower (S : Finset ℕ) (a : ℕ → ℝ) (g : ℕ → ℕ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {R Z v N : ℕ} (hR : 1 ≤ R) (hZ : 1 ≤ Z)
    (hv : R^3*Z ≤ v) {X E C : ℝ} (hE : 0 ≤ E) (hC : 0 < C) (hX : (N:ℝ)/2 ≤ X)
    (hmain : 1/(2*sieveMass R) ≤ lowerMain R Z)
    (hbudget : E ≤ (N:ℝ)/(16*v))
    (hcap : ∀ n ∈ S, (g n).Coprime Z.factorial → majorant R (g n) ≤ C)
    (hrows : ∀ d : ℕ, 0 < d → d ≤ R^2*Z → |row S a g d-X/d| ≤ E) :
    (N:ℝ)/(24*C*(1+Real.log (R+1:ℕ))) ≤
      ∑ n ∈ S, if (g n).Coprime Z.factorial then a n else 0 := by
  apply le_trans _ (rough_weight_positive_cap S a g ha hR hZ hv hE hC hX hmain hbudget hcap hrows)
  have hG : 0 < sieveMass R := lt_of_lt_of_le (by norm_num) (one_le_sieveMass hR)
  apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
  have hh := mul_le_mul_of_nonneg_left (sieveMass_log_upper R) (show 0 ≤ 8*C by positivity)
  nlinarith only [hh]

#print axioms rough_weight_lower_cap
#print axioms rough_weight_log_lower

end Erdos972CappedLowerSieve
