import Submission.LogarithmicCovariance
import Submission.TypeIPolynomial

/-! Centered covariance of logarithmic divisor profiles. Local divisibility
errors and the small signed logarithmic slopes are kept separate. -/
namespace Erdos972LogDivisorProfiles

open Finset Classical
open Erdos972DivisorCovariance Erdos972LogarithmicCovariance Erdos972TypeIPolynomial
open Erdos972PrimePowerError Erdos972DivisorPairCount Erdos972ExponentialSum

set_option maxHeartbeats 1000000

noncomputable def profileMass (D : ℕ) (a b : ℕ → ℝ) := coefficientMass D a+coefficientMass D b
noncomputable def profile (D : ℕ) (a b : ℕ → ℝ) (n : ℕ) :=
  Real.log n*divisorPolynomial D a n+divisorPolynomial D b n
noncomputable def alignedOutput (α : ℝ) (E : ℕ) (c d : ℕ → ℝ) (n : ℕ) :=
  Real.log n*divisorPolynomial E c (floorMul α n)+divisorPolynomial E d (floorMul α n)
noncomputable def model (D : ℕ) (a b : ℕ → ℝ) (n : ℕ) := divisorMean D a*Real.log n+divisorMean D b

def unitCoeff (n : ℕ) : ℝ := if n = 1 then 1 else 0

lemma coefficientMass_nonneg (D : ℕ) (a : ℕ → ℝ) : 0 ≤ coefficientMass D a := sum_nonneg (fun n hn => abs_nonneg _)
lemma profileMass_nonneg (D : ℕ) (a b : ℕ → ℝ) : 0 ≤ profileMass D a b := add_nonneg (coefficientMass_nonneg _ _) (coefficientMass_nonneg _ _)

lemma divisorMean_abs_le (D : ℕ) (a : ℕ → ℝ) : |divisorMean D a| ≤ coefficientMass D a := by
  apply (abs_sum_le_sum_abs _ _).trans
  apply sum_le_sum
  intro d hd
  rw [abs_div, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) d)]
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (mem_Ioc.mp hd).1
  exact div_le_self (abs_nonneg _) hd1

lemma unit_polynomial {D : ℕ} (hD : 0 < D) (n : ℕ) : divisorPolynomial D unitCoeff n = 1 := by
  unfold divisorPolynomial
  rw [sum_eq_single 1]
  · simp [unitCoeff]
  · intro d hd hd1
    simp [unitCoeff, hd1]
  · intro h
    exact (h (mem_Ioc.mpr ⟨by omega, hD⟩)).elim

lemma unit_mean {D : ℕ} (hD : 0 < D) : divisorMean D unitCoeff = 1 := by
  simp only [divisorMean, unitCoeff, ite_div, one_div_one, zero_div, sum_ite_eq', mem_Ioc]
  simp [Nat.ne_of_gt hD]

lemma unit_mass {D : ℕ} (hD : 0 < D) : coefficientMass D unitCoeff = 1 := by
  simp only [coefficientMass, unitCoeff, apply_ite abs, abs_one, abs_zero, sum_ite_eq', mem_Ioc]
  simp [Nat.ne_of_gt hD]

lemma profile_abs_bound (D : ℕ) (a b : ℕ → ℝ) {n N : ℕ} (hn : n ∈ Ioc 0 N) :
    |profile D a b n| ≤ (1+Real.log N)*profileMass D a b := by
  have hln := Real.log_natCast_nonneg n
  have hlN := Real.log_natCast_nonneg N
  unfold profile
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hln]
  have ha := mul_le_mul (monotone_log_natCast (mem_Ioc.mp hn).2) (divisorPolynomial_abs_le D n a)
    (abs_nonneg _) hlN
  have hb := divisorPolynomial_abs_le D n b
  unfold profileMass
  nlinarith only [ha, hb, coefficientMass_nonneg D a, coefficientMass_nonneg D b,
    mul_nonneg hlN (coefficientMass_nonneg D b)]

lemma alignedOutput_abs_bound (α : ℝ) (E : ℕ) (c d : ℕ → ℝ) {n N : ℕ} (hn : n ∈ Ioc 0 N) :
    |alignedOutput α E c d n| ≤ (1+Real.log N)*profileMass E c d := by
  have hln := Real.log_natCast_nonneg n
  have hlN := Real.log_natCast_nonneg N
  unfold alignedOutput
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg hln]
  have ha := mul_le_mul (monotone_log_natCast (mem_Ioc.mp hn).2) (divisorPolynomial_abs_le E (floorMul α n) c)
    (abs_nonneg _) hlN
  have hb := divisorPolynomial_abs_le E (floorMul α n) d
  unfold profileMass
  nlinarith only [ha, hb, coefficientMass_nonneg E c, coefficientMass_nonneg E d,
    mul_nonneg hlN (coefficientMass_nonneg E d)]

lemma model_abs_bound (D : ℕ) (a b : ℕ → ℝ) {n N : ℕ} (hn : n ∈ Ioc 0 N) :
    |model D a b n| ≤ (1+Real.log N)*profileMass D a b := by
  unfold model
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_of_nonneg (Real.log_natCast_nonneg n)]
  have ha := mul_le_mul (divisorMean_abs_le D a) (monotone_log_natCast (mem_Ioc.mp hn).2)
    (Real.log_natCast_nonneg n) (coefficientMass_nonneg D a)
  have hb := divisorMean_abs_le D b
  unfold profileMass
  have hlN := Real.log_natCast_nonneg N
  nlinarith only [ha, hb, coefficientMass_nonneg D a, coefficientMass_nonneg D b,
    mul_nonneg hlN (coefficientMass_nonneg D b)]

lemma four_errors (x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℝ) :
    |(x₁+x₂+x₃+x₄)-(y₁+y₂+y₃+y₄)| ≤ |x₁-y₁|+|x₂-y₂|+|x₃-y₃|+|x₄-y₄| := by
  have he : (x₁+x₂+x₃+x₄)-(y₁+y₂+y₃+y₄) = (x₁-y₁)+(x₂-y₂)+(x₃-y₃)+(x₄-y₄) := by ring
  rw [he]
  exact (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)) le_rfl)

lemma total_profile (N D : ℕ) (a b : ℕ → ℝ) :
    total N (profile D a b) = total N (fun n => Real.log n*divisorPolynomial D a n)+total N (divisorPolynomial D b) := by
  simp only [total, profile, sum_add_distrib]

lemma total_model (N D : ℕ) (a b : ℕ → ℝ) :
    total N (model D a b) = divisorMean D a*(∑ n ∈ Ioc 0 N, Real.log n)+divisorMean D b*(N : ℝ) := by
  simp only [model, total, sum_add_distrib, ← mul_sum, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  ring

lemma profile_first_moment (α : ℝ) {N D E : ℕ} (hE : 0 < E) (a b : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ j ≤ N, ∀ d ∈ Ioc 0 D, ∀ e ∈ Ioc 0 E,
      |((divisorPairs α j d e).card : ℝ)-(j : ℝ)/(d*e)| ≤ B) :
    |total N (profile D a b)-total N (model D a b)| ≤ 2*(1+Real.log N)*B*profileMass D a b := by
  have h₁ := logPower_polynomial_pair_error α N D E 1 a unitCoeff B hlocal
  have h₀ := logPower_polynomial_pair_error α N D E 0 b unitCoeff B hlocal
  simp only [unit_polynomial hE, unit_mean hE, unit_mass hE, pow_one, pow_zero, mul_one,
    one_mul, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at h₁ h₀
  have he : total N (profile D a b)-total N (model D a b) =
      ((∑ n ∈ Ioc 0 N, Real.log n*divisorPolynomial D a n)-divisorMean D a*(∑ n ∈ Ioc 0 N, Real.log n))+
        ((∑ n ∈ Ioc 0 N, divisorPolynomial D b n)-divisorMean D b*N) := by
    rw [total_profile, total_model]
    unfold total
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  have ha := coefficientMass_nonneg D a
  have hb := coefficientMass_nonneg D b
  have hl := Real.log_natCast_nonneg N
  unfold profileMass
  nlinarith only [h₁, h₀, mul_nonneg hB ha, mul_nonneg hB hb, mul_nonneg hl (mul_nonneg hB hb)]

lemma aligned_first_moment (α : ℝ) {N D E : ℕ} (hD : 0 < D) (c d : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 D, ∀ b ∈ Ioc 0 E,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ B) :
    |total N (alignedOutput α E c d)-total N (model E c d)| ≤ 2*(1+Real.log N)*B*profileMass E c d := by
  have h₁ := logPower_polynomial_pair_error α N D E 1 unitCoeff c B hlocal
  have h₀ := logPower_polynomial_pair_error α N D E 0 unitCoeff d B hlocal
  simp only [unit_polynomial hD, unit_mean hD, unit_mass hD, pow_one, pow_zero, mul_one,
    one_mul, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at h₁ h₀
  have he : total N (alignedOutput α E c d)-total N (model E c d) =
      ((∑ n ∈ Ioc 0 N, Real.log n*divisorPolynomial E c (floorMul α n))-divisorMean E c*(∑ n ∈ Ioc 0 N, Real.log n))+
        ((∑ n ∈ Ioc 0 N, divisorPolynomial E d (floorMul α n))-divisorMean E d*N) := by
    rw [total_model]
    simp only [total, alignedOutput, sum_add_distrib]
    ring
  rw [he]
  apply (abs_add_le _ _).trans
  have hc := coefficientMass_nonneg E c
  have hd := coefficientMass_nonneg E d
  have hl := Real.log_natCast_nonneg N
  unfold profileMass
  nlinarith only [h₁, h₀, mul_nonneg hB hc, mul_nonneg hB hd, mul_nonneg hl (mul_nonneg hB hd)]

lemma profile_pair_first_moment (α : ℝ) (N D E : ℕ) (a b c d : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 D, ∀ b ∈ Ioc 0 E,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ B) :
    |total N (fun n => profile D a b n*alignedOutput α E c d n)-
      total N (fun n => model D a b n*model E c d n)| ≤
        2*(1+Real.log N)^2*B*profileMass D a b*profileMass E c d := by
  let Z (k : ℕ) (a b : ℕ → ℝ) :=
    ∑ n ∈ Ioc 0 N, (Real.log n)^k*(divisorPolynomial D a n*divisorPolynomial E b (floorMul α n))
  let W (k : ℕ) (a b : ℕ → ℝ) :=
    (divisorMean D a*divisorMean E b)*(∑ n ∈ Ioc 0 N, (Real.log n)^k)
  have hstep (k : ℕ) (hk : k ≤ 2) (a b : ℕ → ℝ) :
      |Z k a b-W k a b| ≤ 2*(1+Real.log N)^2*B*coefficientMass D a*coefficientMass E b := by
    have hh := logPower_polynomial_pair_error α N D E k a b B hlocal
    have hpow : (Real.log N)^k ≤ (1+Real.log N)^2 := by
      exact (pow_le_pow_left₀ (Real.log_natCast_nonneg N) (by linarith) k).trans
        (pow_le_pow_right₀ (by linarith [Real.log_natCast_nonneg N]) hk)
    have hC : 0 ≤ B*coefficientMass D a*coefficientMass E b := by
      positivity [coefficientMass_nonneg D a, coefficientMass_nonneg E b]
    exact hh.trans (by nlinarith only [mul_le_mul_of_nonneg_right hpow hC])
  have he₁ : total N (fun n => profile D a b n*alignedOutput α E c d n) =
      Z 2 a c+Z 1 a d+Z 1 b c+Z 0 b d := by
    simp only [total, Z, ← sum_add_distrib, profile, alignedOutput]
    apply sum_congr rfl
    intro n hn
    ring
  have he₂ : total N (fun n => model D a b n*model E c d n) =
      W 2 a c+W 1 a d+W 1 b c+W 0 b d := by
    simp only [total, W, mul_sum, ← sum_add_distrib, model]
    apply sum_congr rfl
    intro n hn
    ring
  rw [he₁, he₂]
  have hh := four_errors (Z 2 a c) (Z 1 a d) (Z 1 b c) (Z 0 b d) (W 2 a c) (W 1 a d) (W 1 b c) (W 0 b d)
  apply hh.trans
  have h₁ := hstep 2 le_rfl a c
  have h₂ := hstep 1 (by omega) a d
  have h₃ := hstep 1 (by omega) b c
  have h₄ := hstep 0 (by omega) b d
  unfold profileMass
  nlinarith only [h₁, h₂, h₃, h₄]

/-- The two logarithmic profiles have small centered covariance apart from the
product of their signed logarithmic slopes. -/
theorem aligned_profile_covariance (α : ℝ) {N D E : ℕ} (hN : 0 < N) (hD : 0 < D) (hE : 0 < E)
    (a b c d : ℕ → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 D, ∀ b ∈ Ioc 0 E,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ B) :
    |covariance N (profile D a b) (alignedOutput α E c d)| ≤
      32*(N : ℝ)*|divisorMean D a*divisorMean E c|+
        6*(1+Real.log N)^2*B*profileMass D a b*profileMass E c d := by
  have hf := profile_first_moment α hE a b hB hlocal
  have hg := aligned_first_moment α hD c d hB hlocal
  have hfg := profile_pair_first_moment α N D E a b c d hB hlocal
  have hh := covariance_error_bound hN (profile D a b) (alignedOutput α E c d) (model D a b) (model E c d)
    (by positivity [Real.log_natCast_nonneg N, profileMass_nonneg D a b])
    (by positivity [Real.log_natCast_nonneg N, profileMass_nonneg E c d]) hf hg hfg
    (fun n hn => model_abs_bound D a b hn) (fun n hn => alignedOutput_abs_bound α E c d hn)
  have hm : covariance N (model D a b) (model E c d) =
      (divisorMean D a*divisorMean E c)*logVariance N := covariance_affine_log N _ _ _ _
  have hmabs : |covariance N (model D a b) (model E c d)| ≤ 32*(N : ℝ)*|divisorMean D a*divisorMean E c| := by
    rw [hm, abs_mul, abs_of_nonneg (logVariance_bounds N).1]
    have hb := mul_le_mul_of_nonneg_left (logVariance_bounds N).2 (abs_nonneg (divisorMean D a*divisorMean E c))
    nlinarith only [hb]
  have ht := abs_sub_le (covariance N (profile D a b) (alignedOutput α E c d)) (covariance N (model D a b) (model E c d)) 0
  simp only [sub_zero] at ht
  nlinarith only [hh, hmabs, ht]

#print axioms aligned_profile_covariance

end Erdos972LogDivisorProfiles
