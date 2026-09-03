import Submission.PrimeOutputDilationReduction

/-!
An actual support bound for the Möbius--prime-output sum. It is not a signed
cancellation theorem and does not settle Erdős 972. The loss of mass at inputs
divisible by 4 or 9 gives the explicit constant 2/3 on selected good scales.
-/
namespace Erdos972SquarefreePrimeOutputBound

open Finset Filter ArithmeticFunction
open scoped Topology
open Erdos972WeightedDivisorAmplification Erdos972PrimeOutputAmplificationScales
open Erdos972PrimeOutputDilationReduction Erdos972PrimeGcdRows
open Erdos972PrimePowerError Erdos972ChebyshevRowMean Erdos972CenteredRowScales
open Erdos972CovarianceScaleBudgets Erdos972CommonCovarianceScales
open Erdos972PolynomialRowScales Erdos972WeightedBeattyRows
open Erdos972PrimeCovarianceObstruction Erdos972DivisorCovariance

set_option maxHeartbeats 1500000

lemma moebius_zero_of_four_dvd {n : ℕ} (h : 4 ∣ n) : moebius n = 0 := by
  apply moebius_eq_zero_of_not_squarefree
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs 2 Nat.prime_two) h

lemma moebius_zero_of_nine_dvd {n : ℕ} (h : 9 ∣ n) : moebius n = 0 := by
  apply moebius_eq_zero_of_not_squarefree
  intro hs
  exact (Nat.squarefree_iff_prime_squarefree.mp hs 3 (by decide)) h

lemma moebius_support_bound (n : ℕ) :
    |(moebius n : ℝ)| ≤ 1 - divisorIndicator 4 n - divisorIndicator 9 n +
      divisorIndicator 36 n := by
  have h36 : 36 ∣ n ↔ 4 ∣ n ∧ 9 ∣ n := by
    simpa only [show Nat.lcm 4 9 = 36 by decide] using (Nat.lcm_dvd_iff (m := 4) (n := 9) (k := n))
  by_cases h4 : 4 ∣ n
  · rw [moebius_zero_of_four_dvd h4]
    by_cases h9 : 9 ∣ n <;> simp [divisorIndicator, h4, h9, h36]
  · by_cases h9 : 9 ∣ n
    · rw [moebius_zero_of_nine_dvd h9]
      simp [divisorIndicator, h4, h9, h36]
    · simp only [divisorIndicator, h4, h9, h36, false_and, ↓reduceIte, sub_zero, add_zero]
      exact_mod_cast abs_moebius_le_one (n := n)

lemma weighted_moebius_support_bound (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ S, 0 ≤ a n) :
    (∑ n ∈ S, a n * |(moebius n : ℝ)|) ≤
      divisorRow S a 1 - divisorRow S a 4 - divisorRow S a 9 + divisorRow S a 36 := by
  have hi (d n : ℕ) : a n * divisorIndicator d n = if d ∣ n then a n else 0 := by
    by_cases h : d ∣ n <;> simp [divisorIndicator, h]
  calc
    _ ≤ ∑ n ∈ S, a n * (1 - divisorIndicator 4 n - divisorIndicator 9 n +
        divisorIndicator 36 n) :=
      sum_le_sum fun n hn => mul_le_mul_of_nonneg_left (moebius_support_bound n) (ha n hn)
    _ = _ := by
      simp only [mul_add, mul_sub, mul_one, hi, sum_add_distrib, sum_sub_distrib,
        divisorRow, one_dvd, ↓reduceIte]

lemma signed_moebius_support_bound (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ S, 0 ≤ a n) :
    |∑ n ∈ S, a n * (moebius n : ℝ)| ≤
      divisorRow S a 1 - divisorRow S a 4 - divisorRow S a 9 + divisorRow S a 36 := by
  apply (abs_sum_le_sum_abs _ _).trans
  simp_rw [abs_mul]
  have he : (∑ n ∈ S, |a n| * |(moebius n : ℝ)|) =
      ∑ n ∈ S, a n * |(moebius n : ℝ)| :=
    sum_congr rfl fun n hn => by rw [abs_of_nonneg (ha n hn)]
  rw [he]
  exact weighted_moebius_support_bound S a ha

lemma support_bound_of_rows (S : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ n ∈ S, 0 ≤ a n) {X E : ℝ}
    (h1 : |divisorRow S a 1 - X| ≤ E)
    (h4 : |divisorRow S a 4 - X/4| ≤ E)
    (h9 : |divisorRow S a 9 - X/9| ≤ E)
    (h36 : |divisorRow S a 36 - X/36| ≤ E) :
    |∑ n ∈ S, a n * (moebius n : ℝ)| ≤ (2/3)*X + 4*E := by
  have hs := signed_moebius_support_bound S a ha
  have h₁ := (abs_le.mp h1).2
  have h₄ := (abs_le.mp h4).1
  have h₉ := (abs_le.mp h9).1
  have h₃₆ := (abs_le.mp h36).2
  linarith

/-- Fixed finite divisor rows can be centered at N itself, using the verified
PNT for the common Chebyshev center. There is no new distribution hypothesis. -/
theorem exists_small_centered_output_rows {α η : ℝ} (hα : 1 < α)
    (hI : Irrational α) (hη : 0 < η) (M B : ℕ) :
    ∃ N : ℕ, B < N ∧ ∀ d : ℕ, 0 < d → d ≤ M →
      |divisorRow (Ioc 0 N) (outputWeight α) d - (N : ℝ)/d| ≤ η*N := by
  have hα0 : 0 < α := by linarith
  have hη2 : 0 < η/2 := by positivity
  have hlim : Tendsto (fun u => outputRowBudget α u / scaleCutoff α u)
      atTop (𝓝 0) := output_row_error_budget_tendsto hα.le
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    ((eventually_bound_of_scaled_limit hα.le (outputRowBudget α) hlim hη2).and
      (root64_tendsto.eventually_ge_atTop M))
  have hm : Tendsto (fun N : ℕ => |rowMean α N/(N : ℝ)-1|) atTop (𝓝 0) := by
    simpa using ((rowMean_div_tendsto hα0).sub_const 1).abs
  obtain ⟨K, hK⟩ := eventually_atTop.mp ((tendsto_order.mp hm).2 (η/2) hη2)
  obtain ⟨u, hu, hαu, hv, hrows, _⟩ :=
    exists_joint_prime_divisor_scale hα hI (max B (max T K))
  have hu0 : 0 < u := (Nat.zero_le _).trans_lt hu
  have hαu' : α ≤ u := by linarith
  have huN := (scaleCutoff_bounds hα.le hu0 hαu').1
  have hN : 0 < scaleCutoff α u := hu0.trans_le huN
  have hNR : (0 : ℝ) < scaleCutoff α u := Nat.cast_pos.mpr hN
  have hTu : T ≤ u := (le_max_left T K).trans ((le_max_right B (max T K)).trans hu.le)
  obtain ⟨hbudget, hM⟩ := hT u hTu
  have hKu : K ≤ u := (le_max_right T K).trans ((le_max_right B (max T K)).trans hu.le)
  have hmean : |rowMean α (scaleCutoff α u) - (scaleCutoff α u : ℝ)| ≤
      (η/2)*scaleCutoff α u := by
    have hh := (hK _ (hKu.trans huN)).le
    have hid : rowMean α (scaleCutoff α u)/(scaleCutoff α u : ℝ)-1 =
        (rowMean α (scaleCutoff α u)-(scaleCutoff α u : ℝ))/(scaleCutoff α u : ℝ) := by
      field_simp
    rw [hid, abs_div, abs_of_pos hNR] at hh
    exact (div_le_iff₀ hNR).mp hh
  have hE0 : 0 ≤ polynomialRowError u (root64 u) := by
    unfold polynomialRowError
    positivity [Erdos972PrimeRotation.rotationConstant_pos 256, Real.log_natCast_nonneg u]
  refine ⟨scaleCutoff α u, ((le_max_left B (max T K)).trans_lt hu).trans_le huN, ?_⟩
  intro d hd hdM
  have hrow := prime_divisor_prefix_error hα hI hE0 hN hd
    (j := scaleCutoff α u) le_rfl (by
      intro Q hQ
      rw [outputRow_mangoldt]
      exact hrows d hd (hdM.trans hM) Q
        (hQ.trans (scaleCutoff_row_eligible hα.le u d (scaleCutoff α u / d) le_rfl)))
  have hrow' : |divisorRow (Ioc 0 (scaleCutoff α u)) (outputWeight α) d -
      rowMean α (scaleCutoff α u)/d| ≤ (η/2)*scaleCutoff α u := by
    apply hrow.trans
    exact (by unfold outputRowBudget at hbudget; linarith)
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hc : |rowMean α (scaleCutoff α u)/d - (scaleCutoff α u : ℝ)/d| ≤
      (η/2)*scaleCutoff α u := by
    rw [← sub_div, abs_div, abs_of_pos hd0]
    exact (div_le_div_of_nonneg_right hmean hd0.le).trans
      (div_le_self (by positivity) hdR)
  have ht := abs_sub_le (divisorRow (Ioc 0 (scaleCutoff α u)) (outputWeight α) d)
    (rowMean α (scaleCutoff α u)/d) ((scaleCutoff α u : ℝ)/d)
  linarith only [ht, hrow', hc]

/-- A strict support bound, NOT cancellation: the constant 2/3 is the product
(1-1/4)(1-1/9). This is not a prime-input Mangoldt correlation lower bound. -/
theorem exists_moebius_output_support_bound {α ε : ℝ} (hα : 1 < α)
    (hI : Irrational α) (hε : 0 < ε) (B : ℕ) :
    ∃ N : ℕ, B < N ∧ |moebiusOutputSum α N| ≤ (2/3+ε)*N := by
  obtain ⟨N, hBN, hrows⟩ := exists_small_centered_output_rows hα hI
    (show 0 < ε/4 by positivity) 36 B
  have h1 := hrows 1 (by norm_num) (by norm_num)
  have h4 := hrows 4 (by norm_num) (by norm_num)
  have h9 := hrows 9 (by norm_num) (by norm_num)
  have h36 := hrows 36 (by norm_num) le_rfl
  norm_num only [Nat.cast_one, Nat.cast_ofNat, div_one] at h1 h4 h9 h36
  have hh := support_bound_of_rows (Ioc 0 N) (outputWeight α)
    (fun n _ => vonMangoldt_nonneg) h1 h4 h9 h36
  refine ⟨N, hBN, ?_⟩
  change |∑ n ∈ Ioc 0 N, outputWeight α n * (moebius n : ℝ)| ≤ _
  convert hh using 1; ring

#print axioms exists_small_centered_output_rows
#print axioms exists_moebius_output_support_bound
#print axioms weighted_moebius_support_bound

end Erdos972SquarefreePrimeOutputBound
