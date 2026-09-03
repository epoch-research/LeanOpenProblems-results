import Submission.GcdWeightedRows
import Submission.CovariancePerturbation

/-! Centered covariance estimates for nonlinear gcd profiles. The finite
modulus and all row-error costs remain explicit. -/
namespace Erdos972GcdProfileCovariance

open Finset
open Erdos972GcdProfileExpansion Erdos972GcdWeightedRows
open Erdos972LipschitzLogWeights Erdos972LogarithmicCovariance
open Erdos972ExponentialSum

noncomputable def gcdWeight (F : ℕ) (Φ : ℕ → ℝ → ℝ) (n : ℕ) : ℝ :=
  Φ (n.gcd F) (Real.log n)

lemma constant_divisor_row_error (j : ℕ) {d : ℕ} (hd : 0 < d) :
    |(∑ n ∈ Ioc 0 j, if d ∣ n then (1:ℝ) else 0)-(j:ℝ)/d| ≤ 1 := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one, Nat.Ioc_filter_dvd_card_eq_div]
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hd
  have hlo : ((j/d:ℕ):ℝ) ≤ (j:ℝ)/d := Nat.cast_div_le
  have hhi : (j:ℝ)/d ≤ (j/d:ℕ)+1 := by
    apply (div_le_iff₀ hdR).mpr
    have hh : (j:ℝ) ≤ (d:ℝ)*((j/d:ℕ)+1) := by exact_mod_cast (Nat.lt_mul_div_succ j hd).le
    nlinarith only [hh]
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  linarith only [hhi]

lemma meanProfile_abs_le {F : ℕ} (hF : F ≠ 0) (Φ : ℕ → ℝ → ℝ) (x : ℝ)
    {H : ℝ} (hΦ : ∀ r ∈ F.divisors, |Φ r x| ≤ H) : |meanProfile F Φ x| ≤ H := by
  have hFR : (0 : ℝ) < F := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hF)
  rw [meanProfile, abs_div, abs_of_pos hFR]
  apply (div_le_iff₀ hFR).mpr
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ n ∈ Ioc 0 F, H := sum_le_sum (fun n _ => hΦ _ (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n F, hF⟩))
    _ = _ := by simp [mul_comm]

lemma logProfile_abs_bound {F N : ℕ} (Φ : ℕ → ℝ → ℝ) {H L : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ r ∈ F.divisors, ∀ x y, |Φ r x-Φ r y| ≤ L*|x-y|)
    (hend : ∀ r ∈ F.divisors, |Φ r (Real.log N)| ≤ H)
    {r n : ℕ} (hr : r ∈ F.divisors) (hn : n ∈ Ioc 0 N) :
    |Φ r (Real.log n)| ≤ H+L*Real.log N := by
  have hlog := monotone_log_natCast (mem_Ioc.mp hn).2
  have hh := hΦ r hr (Real.log n) (Real.log N)
  rw [abs_of_nonpos (sub_nonpos.mpr hlog)] at hh
  have ht := abs_sub_le (Φ r (Real.log n)) (Φ r (Real.log N)) 0
  simp only [sub_zero] at ht
  have hp := mul_nonneg hL (Real.log_natCast_nonneg n)
  linarith only [hh, ht, hend r hr, hp]

lemma centered_model_identity (Φ : ℝ → ℝ) (X : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, Φ (Real.log n)*(X n-X (n-1)))-
      (∑ n ∈ Ioc 0 N, Φ (Real.log n))*X N/N = centeredLogWeight Φ X N := by
  simp only [centeredLogWeight, sum_Ioc_zero_eq_sum_range_succ, Nat.add_sub_cancel,
    mul_sub, sum_sub_distrib, ← sum_mul, mul_div_assoc]

lemma covariance_three_errors {P P₀ A A₀ B B₀ n e₁ e₂ e₃ K C : ℝ}
    (h₁ : |P-P₀| ≤ e₁) (h₂ : |A-A₀| ≤ e₂) (h₃ : |B-B₀| ≤ e₃)
    (hA : |A/n| ≤ K) (hB : |B₀/n| ≤ C) :
    |(P-A*B/n)-(P₀-A₀*B₀/n)| ≤ e₁+K*e₃+C*e₂ := by
  have he : (P-A*B/n)-(P₀-A₀*B₀/n) = (P-P₀)-(A/n)*(B-B₀)-(B₀/n)*(A-A₀) := by ring
  rw [he]
  apply ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
  rw [abs_mul, abs_mul]
  have hk := mul_le_mul hA h₃ (abs_nonneg _) ((abs_nonneg _).trans hA)
  have hc := mul_le_mul hB h₂ (abs_nonneg _) ((abs_nonneg _).trans hB)
  linarith only [h₁, hk, hc]

/-- The centering budget has no factor equal to the number of patterns;
that cost occurs only in the explicit divisibility-row errors. -/
theorem gcd_covariance_bound {F N : ℕ} (hF : F ≠ 0) (hN : 0 < N)
    (Φ : ℕ → ℝ → ℝ) (a X : ℕ → ℝ) (hX0 : X 0 = 0)
    {H L E C c : ℝ} (hL : 0 ≤ L)
    (hΦ : ∀ r ∈ F.divisors, ∀ x y, |Φ r x-Φ r y| ≤ L*|x-y|)
    (hend : ∀ r ∈ F.divisors, |Φ r (Real.log N)| ≤ H)
    (hX : |X N/N| ≤ C)
    (hrows : ∀ d ∈ F.divisors, ∀ j ≤ N,
      |(∑ n ∈ Ioc 0 j, if d ∣ n then a n else 0)-X j/d| ≤ E) :
    |covariance N (gcdWeight F Φ) a| ≤
      L*centeredMeanBudget X c N+
        (H+L*Real.log N)*(profileCost F*(E+C)+E) := by
  let K := H+L*Real.log N
  let Q : ℕ → ℝ := fun n => meanProfile F Φ (Real.log n)
  have hNR : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have hmean : |total N (gcdWeight F Φ)/N| ≤ K := by
    rw [abs_div, abs_of_pos hNR]
    apply (div_le_iff₀ hNR).mpr
    have hh := total_abs_le (fun n hn =>
      logProfile_abs_bound Φ hL hΦ hend (Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n F, hF⟩) hn)
    exact hh.trans_eq (by ring)
  have hmain := weighted_gcd_row_error hF hN Φ a X hX0 hL hΦ hend hrows
  have hfirst := weighted_gcd_row_error hF hN Φ (fun _ => 1) (fun j : ℕ => (j:ℝ))
    (by simp) hL hΦ hend (E := 1) (by
      intro d hd j hj
      exact constant_divisor_row_error j (Nat.pos_of_mem_divisors hd))
  have hinc (n : ℕ) (hn : n ∈ Ioc 0 N) : (n:ℝ)-(n-1:ℕ) = 1 := by
    rw [Nat.cast_sub (mem_Ioc.mp hn).1]
    norm_num
  have hsum : (∑ n ∈ Ioc 0 N, meanProfile F Φ (Real.log n)*((n:ℝ)-(n-1:ℕ))) = total N Q := by
    apply sum_congr rfl
    intro n hn
    rw [hinc n hn, mul_one]
  rw [hsum] at hfirst
  have hfirst' : |total N (gcdWeight F Φ)-total N Q| ≤ profileCost F*K := by
    simpa only [mul_one, total, Q, gcdWeight, K] using hfirst
  have hlast : |total N a-X N| ≤ E := by
    simpa only [one_dvd, if_true, Nat.cast_one, div_one, total] using
      hrows 1 (Nat.mem_divisors.mpr ⟨one_dvd F, hF⟩) N le_rfl
  have herr := covariance_three_errors hmain hfirst' hlast hmean hX
  have hcenter := centeredLogWeight_bound (meanProfile F Φ) hL (meanProfile_lipschitz hF Φ hΦ) X hX0 c N
  have he : (∑ n ∈ Ioc 0 N, meanProfile F Φ (Real.log n)*(X n-X (n-1)))-
      total N Q*X N/N = centeredLogWeight (meanProfile F Φ) X N :=
    centered_model_identity _ _ _
  change |covariance N (gcdWeight F Φ) a-
    ((∑ n ∈ Ioc 0 N, meanProfile F Φ (Real.log n)*(X n-X (n-1)))-total N Q*X N/N)| ≤ _ at herr
  rw [he] at herr
  have ht := abs_sub_le (covariance N (gcdWeight F Φ) a) (centeredLogWeight (meanProfile F Φ) X N) 0
  simp only [sub_zero] at ht
  dsimp only [K] at herr
  nlinarith only [ht, herr, hcenter]

#print axioms gcd_covariance_bound

end Erdos972GcdProfileCovariance
