import Submission.LogDivisorProfiles
import Submission.CovariancePerturbation
import Submission.WeightedBeattyRows

/-! Passage from the common input logarithm to the actual output logarithm. -/
namespace Erdos972ProfileLogShift

open Finset
open Erdos972DivisorCovariance Erdos972LogarithmicCovariance Erdos972TypeIPolynomial
open Erdos972LogDivisorProfiles Erdos972CovariancePerturbation
open Erdos972PrimePowerError Erdos972WeightedBeattyRows Erdos972DivisorPairCount

lemma divisorPolynomial_linear (E : ℕ) (γ : ℝ) (c d : ℕ → ℝ) (q : ℕ) :
    divisorPolynomial E (fun k => γ*c k+d k) q =
      γ*divisorPolynomial E c q+divisorPolynomial E d q := by
  simp only [divisorPolynomial, mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  split_ifs <;> ring

lemma coefficientMass_linear (E : ℕ) (γ : ℝ) (c d : ℕ → ℝ) :
    coefficientMass E (fun k => γ*c k+d k) ≤
      |γ| *coefficientMass E c+coefficientMass E d := by
  simp only [coefficientMass, mul_sum, ← sum_add_distrib]
  apply sum_le_sum
  intro k hk
  simpa only [abs_mul] using abs_add_le (γ*c k) (d k)

lemma profileMass_shift (E : ℕ) (γ : ℝ) (c d : ℕ → ℝ) :
    profileMass E c (fun k => γ*c k+d k) ≤ (1+|γ|)*profileMass E c d := by
  have hh := coefficientMass_linear E γ c d
  unfold profileMass
  nlinarith only [hh, mul_nonneg (abs_nonneg γ) (coefficientMass_nonneg E d)]

lemma profile_log_shift_identity (α : ℝ) (E : ℕ) (c d : ℕ → ℝ) (n : ℕ) :
    profile E c d (floorMul α n)-alignedOutput α E c (fun k => Real.log α*c k+d k) n =
      (Real.log (floorMul α n)-Real.log n-Real.log α)*divisorPolynomial E c (floorMul α n) := by
  unfold profile alignedOutput
  rw [divisorPolynomial_linear]
  ring

lemma profile_log_shift_pointwise {α : ℝ} (hα : 1 ≤ α) (E : ℕ) (c d : ℕ → ℝ)
    {n : ℕ} (hn : 0 < n) :
    |profile E c d (floorMul α n)-alignedOutput α E c (fun k => Real.log α*c k+d k) n| ≤
      coefficientMass E c*(1/(n : ℝ)) := by
  have hg := log_floorMul_gap hα hn
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hqR : (0 : ℝ) < floorMul α n := Nat.cast_pos.mpr (floorMul_pos hα hn)
  have hrec : 1/(floorMul α n : ℝ) ≤ 1/(n : ℝ) :=
    one_div_le_one_div_of_le hnR (Nat.cast_le.mpr (self_le_floorMul hα n))
  rw [profile_log_shift_identity, abs_mul]
  have he : |Real.log (floorMul α n)-Real.log n-Real.log α| =
      Real.log α+Real.log n-Real.log (floorMul α n) := by
    rw [abs_of_nonpos (by linarith only [hg.1])]
    ring
  rw [he]
  exact (mul_le_mul (hg.2.trans hrec) (divisorPolynomial_abs_le E _ c)
    (abs_nonneg _) (by positivity)).trans_eq (by ring)

/-- The logarithm replacement error has bounded harmonic mass. -/
theorem profile_log_shift_l1 {α : ℝ} (hα : 1 ≤ α) (N E : ℕ) (c d : ℕ → ℝ) :
    total N (fun n =>
      |profile E c d (floorMul α n)-alignedOutput α E c (fun k => Real.log α*c k+d k) n|) ≤
        coefficientMass E c*(1+Real.log N) := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, coefficientMass E c*(1/(n : ℝ)) := by
      apply sum_le_sum
      intro n hn
      exact profile_log_shift_pointwise hα E c d (mem_Ioc.mp hn).1
    _ = coefficientMass E c*(∑ n ∈ Ioc 0 N, 1/(n : ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_Ioc_bound N) (coefficientMass_nonneg E c)

/-- Covariance of the actual two profiles, not merely the common-logarithm
models. The two signed slopes are unchanged by the logarithm replacement. -/
theorem profile_covariance {α : ℝ} (hα : 1 ≤ α) {N D E : ℕ}
    (hN : 0 < N) (hD : 0 < D) (hE : 0 < E) (a b c d : ℕ → ℝ)
    {B : ℝ} (hB : 0 ≤ B)
    (hlocal : ∀ j ≤ N, ∀ a ∈ Ioc 0 D, ∀ b ∈ Ioc 0 E,
      |((divisorPairs α j a b).card : ℝ)-(j : ℝ)/(a*b)| ≤ B) :
    |covariance N (profile D a b) (fun n => profile E c d (floorMul α n))| ≤
      32*(N : ℝ)*|divisorMean D a*divisorMean E c|+
        6*(1+Real.log N)^2*B*profileMass D a b*
          profileMass E c (fun k => Real.log α*c k+d k)+
        2*(1+Real.log N)^2*profileMass D a b*coefficientMass E c := by
  let G := alignedOutput α E c (fun k => Real.log α*c k+d k)
  have hcov := aligned_profile_covariance α hN hD hE a b c
    (fun k => Real.log α*c k+d k) hB hlocal
  have hp := covariance_second_perturb hN (profile D a b)
    (fun n => profile E c d (floorMul α n)) G (fun n hn => profile_abs_bound D a b hn)
  have hmul := mul_le_mul_of_nonneg_left (profile_log_shift_l1 hα N E c d)
    (show 0 ≤ 2*((1+Real.log N)*profileMass D a b) by
      positivity [Real.log_natCast_nonneg N, profileMass_nonneg D a b])
  have ht := abs_sub_le
    (covariance N (profile D a b) (fun n => profile E c d (floorMul α n)))
    (covariance N (profile D a b) G) 0
  simp only [sub_zero] at ht
  dsimp [G] at hp ht
  nlinarith only [hcov, hp, hmul, ht]

#print axioms profile_covariance

end Erdos972ProfileLogShift
