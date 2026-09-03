import Submission.LargePrimeMoments

/-!
# Finite distributions with prescribed initial binomial moments

A nonnegative moment sequence satisfying (k+1) M(k+1) <= M(k) admits a
probability model supported on {0,...,R}, matching every moment up to R.
In particular, exact initial Poisson moments do not force a nonzero higher
moment. These are abstract models, not models asserted to describe primes.
-/

open Nat Finset
open scoped Classical BigOperators

namespace Erdos821

set_option maxHeartbeats 2000000

noncomputable def truncatedMomentWeight (R : ℕ) (M : ℕ → ℝ) (k : ℕ) : ℝ :=
  if _hk : k ≤ R then
    M k - ∑ j ∈ (Icc (k + 1) R).attach,
      ((j.val).choose k : ℝ) * truncatedMomentWeight R M j.val
  else 0
termination_by R + 1 - k
decreasing_by
  have h := Finset.mem_Icc.mp j.property
  omega

lemma truncatedMomentWeight_eq (R : ℕ) (M : ℕ → ℝ) (k : ℕ) (hk : k ≤ R) :
    truncatedMomentWeight R M k =
      M k - ∑ j ∈ Icc (k + 1) R, (j.choose k : ℝ) * truncatedMomentWeight R M j := by
  rw [truncatedMomentWeight, dif_pos hk]
  congr 1
  exact Finset.sum_attach (Icc (k + 1) R) (fun j : ℕ => (j.choose k : ℝ) * truncatedMomentWeight R M j)

lemma truncatedMomentWeight_eq_zero (R : ℕ) (M : ℕ → ℝ) (k : ℕ) (hk : R < k) :
    truncatedMomentWeight R M k = 0 := by
  rw [truncatedMomentWeight, dif_neg (by omega)]

lemma truncatedMomentWeight_top (R : ℕ) (M : ℕ → ℝ) :
    truncatedMomentWeight R M R = M R := by
  rw [truncatedMomentWeight_eq R M R le_rfl]
  simp

/-- The triangular recurrence gives the exact requested moment equations. -/
lemma truncatedMomentWeight_moment_Icc (R : ℕ) (M : ℕ → ℝ) (k : ℕ) (hk : k ≤ R) :
    (∑ j ∈ Icc k R, (j.choose k : ℝ) * truncatedMomentWeight R M j) = M k := by
  have hset : Icc k R = insert k (Icc (k + 1) R) := by
    ext j
    simp only [mem_Icc, mem_insert]
    omega
  rw [hset, sum_insert (by simp), Nat.choose_self, Nat.cast_one, one_mul,
    truncatedMomentWeight_eq R M k hk]
  ring

lemma truncatedMomentWeight_moment (R : ℕ) (M : ℕ → ℝ) (k : ℕ) (hk : k ≤ R) :
    (∑ j ∈ range (R + 1), (j.choose k : ℝ) * truncatedMomentWeight R M j) = M k := by
  rw [← truncatedMomentWeight_moment_Icc R M k hk]
  symm
  apply sum_subset
  · intro j hj
    have h := mem_Icc.mp hj
    exact mem_range.mpr (by omega)
  · intro j hj hjk
    have hjR := mem_range.mp hj
    have hjlt : j < k := by
      by_contra h
      exact hjk (mem_Icc.mpr ⟨by omega, by omega⟩)
    rw [Nat.choose_eq_zero_of_lt hjlt, Nat.cast_zero, zero_mul]

lemma choose_le_succ_mul_choose {j k : ℕ} (hkj : k < j) :
    j.choose k ≤ (k + 1) * j.choose (k + 1) := by
  calc
    _ = j.choose k * 1 := (mul_one _).symm
    _ ≤ j.choose k * (j - k) := Nat.mul_le_mul_left _ (by omega)
    _ = _ := by rw [← Nat.choose_succ_right_eq]; ring

/-- Positivity follows from the next moment equation and a union-bound
inequality for binomial coefficients. -/
theorem truncatedMomentWeight_nonneg (R : ℕ) (M : ℕ → ℝ)
    (hM : ∀ k ≤ R, 0 ≤ M k)
    (hstep : ∀ k < R, ((k + 1 : ℕ) : ℝ) * M (k + 1) ≤ M k) (k : ℕ) :
    0 ≤ truncatedMomentWeight R M k := by
  have H : ∀ r : ℕ, ∀ k : ℕ, R + 1 - k = r → 0 ≤ truncatedMomentWeight R M k := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro k heq
      by_cases hk : k ≤ R
      · by_cases hkeq : k = R
        · subst k
          rw [truncatedMomentWeight_top]
          exact hM R le_rfl
        have hkR : k < R := by omega
        have htail : (∑ j ∈ Icc (k + 1) R, (j.choose k : ℝ) * truncatedMomentWeight R M j) ≤
            ((k + 1 : ℕ) : ℝ) * M (k + 1) := by
          calc
            _ ≤ ∑ j ∈ Icc (k + 1) R,
                (((k + 1 : ℕ) : ℝ) * (j.choose (k + 1) : ℝ)) * truncatedMomentWeight R M j := by
              apply sum_le_sum
              intro j hj
              have hjdata := mem_Icc.mp hj
              have hnonneg := ih (R + 1 - j) (by omega) j rfl
              apply mul_le_mul_of_nonneg_right _ hnonneg
              exact_mod_cast choose_le_succ_mul_choose (by omega : k < j)
            _ = ((k + 1 : ℕ) : ℝ) *
                (∑ j ∈ Icc (k + 1) R, (j.choose (k + 1) : ℝ) * truncatedMomentWeight R M j) := by
              rw [mul_sum]
              exact sum_congr rfl (fun _ _ => by ring)
            _ = _ := by rw [truncatedMomentWeight_moment_Icc R M (k + 1) (by omega)]
        rw [truncatedMomentWeight_eq R M k hk]
        linarith only [htail, hstep k hkR]
      · rw [truncatedMomentWeight_eq_zero R M k (by omega)]
  exact H _ k rfl

/-- Existence of a normalized nonnegative model with no tail above R. -/
theorem exists_truncated_binomial_moment_model (R : ℕ) (M : ℕ → ℝ)
    (hM0 : M 0 = 1) (hM : ∀ k ≤ R, 0 ≤ M k)
    (hstep : ∀ k < R, ((k + 1 : ℕ) : ℝ) * M (k + 1) ≤ M k) :
    ∃ w : ℕ → ℝ,
      (∀ j, 0 ≤ w j) ∧ (∀ j, R < j → w j = 0) ∧
      (∑ j ∈ range (R + 1), w j) = 1 ∧
      ∀ k ≤ R, (∑ j ∈ range (R + 1), (j.choose k : ℝ) * w j) = M k := by
  refine ⟨truncatedMomentWeight R M, truncatedMomentWeight_nonneg R M hM hstep,
    truncatedMomentWeight_eq_zero R M, ?_, truncatedMomentWeight_moment R M⟩
  have h := truncatedMomentWeight_moment R M 0 (Nat.zero_le _)
  simpa only [Nat.choose_zero_right, Nat.cast_one, one_mul, hM0] using h

noncomputable def poissonBinomialMoment (μ : ℝ) (k : ℕ) : ℝ := μ^k / (k.factorial : ℝ)

lemma poissonBinomialMoment_step (μ : ℝ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * poissonBinomialMoment μ (k + 1) = μ * poissonBinomialMoment μ k := by
  have hk : (k.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have hk1 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  unfold poissonBinomialMoment
  rw [Nat.factorial_succ, Nat.cast_mul, pow_succ]
  field_simp

/-- Initial Poisson binomial moments can hold exactly even when the next
moment, and the entire tail above R, vanish. -/
theorem exists_truncated_poisson_moment_model (R : ℕ) (μ : ℝ) (hμ : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    ∃ w : ℕ → ℝ,
      (∀ j, 0 ≤ w j) ∧ (∀ j, R < j → w j = 0) ∧
      (∑ j ∈ range (R + 1), w j) = 1 ∧
      ∀ k ≤ R, (∑ j ∈ range (R + 1), (j.choose k : ℝ) * w j) = μ^k / (k.factorial : ℝ) := by
  apply exists_truncated_binomial_moment_model R (poissonBinomialMoment μ)
  · simp [poissonBinomialMoment]
  · intro k hk
    exact div_nonneg (pow_nonneg hμ _) (Nat.cast_nonneg _)
  · intro k hk
    rw [poissonBinomialMoment_step]
    exact mul_le_of_le_one_left (div_nonneg (pow_nonneg hμ _) (Nat.cast_nonneg _)) hμ1

end Erdos821
