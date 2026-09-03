import Submission.DivisorCovariance
import Submission.DoubleVaughan
import Submission.MobiusLaplace

/-! A logarithmic divisor-polynomial representation of Vaughan's Type-I part. -/
namespace Erdos972TypeIPolynomial

open Finset ArithmeticFunction Classical
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open Erdos972Vaughan Erdos972DoubleVaughan Erdos972DivisorCovariance
open Erdos972MobiusPartialSums Erdos972ExponentialSum

lemma truncated_divisor_sum (D n : ℕ) (f : ℕ → ℝ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, if d ≤ D then f d else 0) = divisorPolynomial D f n := by
  classical
  rw [← sum_filter, divisorPolynomial, ← sum_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_Ioc]
  constructor
  · rintro ⟨⟨hdn, hn0⟩, hdD⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hdn hn, hdD⟩, hdn⟩
  · rintro ⟨⟨hd, hdD⟩, hdn⟩
    exact ⟨⟨hdn, Nat.ne_of_gt hn⟩, hdD⟩

lemma supported_divisor_sum (D n : ℕ) (f : ℕ → ℝ) (hn : 0 < n)
    (hf : ∀ d, D < d → f d = 0) :
    (∑ d ∈ n.divisors, f d) = divisorPolynomial D f n := by
  rw [← truncated_divisor_sum D n f hn]
  apply sum_congr rfl
  intro d hd
  by_cases hD : d ≤ D
  · simp only [if_pos hD]
  · rw [if_neg hD, hf d (Nat.lt_of_not_ge hD)]

noncomputable def slopeCoeff (U : ℕ) (d : ℕ) : ℝ := cutoff (μ : ArithmeticFunction ℝ) U d
noncomputable def constantCoeff (U V : ℕ) (d : ℕ) : ℝ :=
  -slopeCoeff U d*Real.log d-(cutoff (μ : ArithmeticFunction ℝ) U*cutoff Λ V) d

lemma slopeCoeff_support {U D : ℕ} (hUD : U ≤ D) {d : ℕ} (hd : D < d) : slopeCoeff U d = 0 :=
  cutoff_eq_zero_of_lt _ (hUD.trans_lt hd)

lemma constantCoeff_support (U V d : ℕ) (hd : U*V < d) (hV : 0 < V) : constantCoeff U V d = 0 := by
  have hUD : U ≤ U*V := by nlinarith
  rw [constantCoeff, slopeCoeff_support hUD hd, cutoff_mul_cutoff_eq_zero_of_lt _ _ U V d hd]
  ring

lemma first_log_divisor_sum (U : ℕ) {n : ℕ} (hn : 0 < n) :
    (cutoff (μ : ArithmeticFunction ℝ) U*ArithmeticFunction.log) n =
      ∑ d ∈ n.divisors, slopeCoeff U d*(Real.log n-Real.log d) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
    (fun d k => cutoff (μ : ArithmeticFunction ℝ) U d*ArithmeticFunction.log k)]
  apply sum_congr rfl
  intro d hd
  have hdn := (Nat.mem_divisors.mp hd).1
  have hdpos := Nat.pos_of_dvd_of_pos hdn hn
  have hdR : (0 : ℝ) < d := Nat.cast_pos.mpr hdpos
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  rw [ArithmeticFunction.log_apply, Nat.cast_div hdn hdR.ne', Real.log_div hnR.ne' hdR.ne']
  rfl

/-- Only two divisor polynomials, one logarithmic, are needed. The isolated
small-input term is kept separate. -/
theorem typeIPart_polynomial (U V : ℕ) (hV : 0 < V) {n : ℕ} (hn : 0 < n) :
    typeIPart U V n =
      Real.log n*divisorPolynomial (U*V) (slopeCoeff U) n+
        divisorPolynomial (U*V) (constantCoeff U V) n+cutoff Λ V n := by
  have hUD : U ≤ U*V := by nlinarith
  have hfirst := first_log_divisor_sum U hn
  have hsecond : (cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V) n =
      ∑ d ∈ n.divisors, (cutoff (μ : ArithmeticFunction ℝ) U*cutoff Λ V) d := by
    rw [show cutoff (μ : ArithmeticFunction ℝ) U*ζ*cutoff Λ V =
      (cutoff (μ : ArithmeticFunction ℝ) U*cutoff Λ V)*ζ by ring, ArithmeticFunction.coe_mul_zeta_apply]
  have ha := supported_divisor_sum (U*V) n (slopeCoeff U) hn (fun d hd => slopeCoeff_support hUD hd)
  have hb := supported_divisor_sum (U*V) n (constantCoeff U V) hn (fun d hd => constantCoeff_support U V d hd hV)
  simp only [typeIPart, ArithmeticFunction.add_apply, Erdos972Vaughan.sub_apply]
  rw [hfirst, hsecond, ← ha, ← hb]
  simp only [constantCoeff, mul_sub, sum_sub_distrib, sum_add_distrib, ← sum_mul, ← mul_sum, neg_mul, sum_neg_distrib]
  ring

lemma abs_slopeCoeff_le (U d : ℕ) : |slopeCoeff U d| ≤ 1 := abs_cutoff_moebius_le_one U d

lemma abs_constantCoeff_le (U V d : ℕ) : |constantCoeff U V d| ≤ 2*Real.log d := by
  unfold constantCoeff
  apply (abs_sub _ _).trans
  rw [abs_mul, abs_neg, abs_of_nonneg (Real.log_natCast_nonneg d)]
  have hh := mul_le_mul_of_nonneg_right (abs_slopeCoeff_le U d) (Real.log_natCast_nonneg d)
  linarith only [hh, abs_typeI_coefficient_le_log U V d]

lemma slopeCoeff_mass (U D : ℕ) : coefficientMass D (slopeCoeff U) ≤ D := by
  apply (sum_le_sum (fun d _ => abs_slopeCoeff_le U d)).trans_eq
  simp

lemma constantCoeff_mass (U V D : ℕ) : coefficientMass D (constantCoeff U V) ≤ 2*(D : ℝ)*Real.log D := by
  calc
    _ ≤ ∑ d ∈ Ioc 0 D, 2*Real.log D := by
      apply sum_le_sum
      intro d hd
      exact (abs_constantCoeff_le U V d).trans (mul_le_mul_of_nonneg_left (monotone_log_natCast (mem_Ioc.mp hd).2) (by norm_num))
    _ = _ := by simp; ring

lemma slopeCoeff_mean {U D : ℕ} (hUD : U ≤ D) : divisorMean D (slopeCoeff U) = reciprocalMoebius U := by
  simp only [divisorMean, slopeCoeff, cutoff_apply, ite_div, zero_div, ArithmeticFunction.intCoe_apply, ← sum_filter]
  have he : (Ioc 0 D).filter (fun d => d ≤ U) = Ioc 0 U := by
    ext d
    simp only [mem_filter, mem_Ioc]
    omega
  rw [he]
  rfl

lemma divisorPolynomial_abs_le (D n : ℕ) (a : ℕ → ℝ) : |divisorPolynomial D a n| ≤ coefficientMass D a := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  split_ifs <;> simp

#print axioms typeIPart_polynomial
#print axioms slopeCoeff_mean

end Erdos972TypeIPolynomial
