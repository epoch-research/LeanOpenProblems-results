import Submission.SelbergNormalizerUpper

/-! Positive radical-tail estimates for the Selberg normalizer.
This file is auxiliary; it does not prove the quadratic Jacobsthal conjecture. -/
namespace Erdos970.FiniteSelberg
open Finset Real

noncomputable def primeRadical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

lemma primeRadical_pos (n : ℕ) : 0 < primeRadical n :=
  prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)

lemma primeRadical_dvd (n : ℕ) : primeRadical n ∣ n := Nat.prod_primeFactors_dvd n

lemma primeRadical_mul {m n : ℕ} (h : m.Coprime n) :
    primeRadical (m * n) = primeRadical m * primeRadical n := by
  unfold primeRadical
  rw [h.primeFactors_mul, prod_union h.disjoint_primeFactors]

noncomputable def radicalHalfWeight (n : ℕ) : ℝ := 1 / (sqrt n * primeRadical n)

lemma radicalHalfWeight_nonneg (n : ℕ) : 0 ≤ radicalHalfWeight n := by
  unfold radicalHalfWeight
  positivity

lemma radicalHalfWeight_mul {m n : ℕ} (h : m.Coprime n) :
    radicalHalfWeight (m * n) = radicalHalfWeight m * radicalHalfWeight n := by
  unfold radicalHalfWeight
  rw [primeRadical_mul h, Nat.cast_mul, Nat.cast_mul, sqrt_mul (Nat.cast_nonneg m)]
  ring

lemma radicalHalfWeight_one : radicalHalfWeight 1 = 1 := by
  simp [radicalHalfWeight, primeRadical]

lemma sqrt_nat_pow (p n : ℕ) : sqrt ((p ^ n : ℕ) : ℝ) = sqrt p ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Nat.cast_mul, sqrt_mul (Nat.cast_nonneg _), ih, pow_succ]

lemma radicalHalfWeight_prime_pow (p n : ℕ) (hp : p.Prime) :
    radicalHalfWeight (p ^ (n + 1)) = (1 / (p : ℝ)) * (1 / sqrt p) ^ (n + 1) := by
  unfold radicalHalfWeight primeRadical
  rw [Nat.primeFactors_prime_pow (by omega) hp, prod_singleton, sqrt_nat_pow]
  simp only [one_div, mul_inv_rev, inv_pow]

lemma sqrt_prime_inv_norm_lt_one (p : ℕ) (hp : p.Prime) : ‖1 / sqrt (p : ℝ)‖ < 1 := by
  have hs : (1 : ℝ) < sqrt p := by
    simpa using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by exact_mod_cast hp.one_lt)
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  exact (div_lt_one (by positivity)).mpr hs

lemma radicalHalfWeight_prime_hasSum (p : ℕ) (hp : p.Prime) :
    HasSum (fun n : ℕ => radicalHalfWeight (p ^ n))
      (1 + 1 / ((p : ℝ) * (sqrt p - 1))) := by
  have h := ((hasSum_geometric_of_norm_lt_one (sqrt_prime_inv_norm_lt_one p hp)).mul_left
    (1 / (p : ℝ))).update 0 1
  have he : (fun n : ℕ => radicalHalfWeight (p ^ n)) =
      Function.update (fun n : ℕ => (1 / (p : ℝ)) * (1 / sqrt p) ^ n) 0 1 := by
    funext n
    cases n with
    | zero => simp [radicalHalfWeight_one]
    | succ n => simpa using radicalHalfWeight_prime_pow p n hp
  rw [he]
  convert h using 1
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hs0 : sqrt (p : ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast hp.pos)).ne'
  have hs1 : sqrt (p : ℝ) - 1 ≠ 0 := by
    have hh : (1 : ℝ) < sqrt p := by
      simpa using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) (by exact_mod_cast hp.one_lt)
    linarith
  simp only [pow_zero, mul_one]
  field_simp
  <;> ring

lemma radicalHalfWeight_factored_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    HasSum (fun n : Nat.factoredNumbers P => radicalHalfWeight n.val)
      (∏ p ∈ P, (1 + 1 / ((p : ℝ) * (sqrt p - 1)))) := by
  have hh := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    radicalHalfWeight_one (fun h => radicalHalfWeight_mul h)
    (fun {p} hp => (radicalHalfWeight_prime_hasSum p hp).summable.norm) P).2
  rw [filter_true_of_mem hP] at hh
  convert hh using 1
  apply prod_congr rfl
  intro p hp
  exact (radicalHalfWeight_prime_hasSum p (hP p hp)).tsum_eq.symm

noncomputable def radicalTailSeries : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ))

lemma radicalTailSeries_summable : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
  summable_nat_rpow.mpr (by norm_num)

lemma sqrt_prime_correction_le (p : ℕ) (hp : p.Prime) :
    1 / ((p : ℝ) * (sqrt p - 1)) ≤ 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hs : (4 / 3 : ℝ) ≤ sqrt p := by
    exact (le_sqrt (by norm_num) hp0.le).mpr (by nlinarith)
  have hs0 : 0 < sqrt (p : ℝ) := sqrt_pos.mpr hp0
  have hpow : (p : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((p : ℝ) * sqrt p) := by
    rw [rpow_neg hp0.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      rpow_add hp0, rpow_one, ← sqrt_eq_rpow]
    simp only [one_div]
  rw [hpow]
  have hh : 0 < sqrt (p : ℝ) - 1 := by linarith
  apply (div_le_iff₀ (mul_pos hp0 hh)).mpr
  have hmul : (4 * (1 / ((p : ℝ) * sqrt p))) * ((p : ℝ) * (sqrt p - 1)) =
      4 * (sqrt p - 1) / sqrt p := by field_simp
  rw [hmul]
  apply (le_div_iff₀ hs0).mpr
  linarith

lemma radicalHalfWeight_factored_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    (∑' n : Nat.factoredNumbers P, radicalHalfWeight n.val) ≤ exp (4 * radicalTailSeries) := by
  rw [(radicalHalfWeight_factored_hasSum P hP).tsum_eq]
  calc
    _ ≤ ∏ p ∈ P, exp (1 / ((p : ℝ) * (sqrt p - 1))) := by
      apply prod_le_prod
      · intro p hp
        have hs : (1 : ℝ) < sqrt p := by
          simpa using sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)
            (by exact_mod_cast (hP p hp).one_lt)
        have hs1 : 0 < sqrt (p : ℝ) - 1 := by linarith
        positivity
      · intro p hp
        simpa only [add_comm] using add_one_le_exp (1 / ((p : ℝ) * (sqrt p - 1)))
    _ = exp (∑ p ∈ P, 1 / ((p : ℝ) * (sqrt p - 1))) := (exp_sum _ _).symm
    _ ≤ exp (4 * radicalTailSeries) := by
      apply exp_le_exp.mpr
      calc
        _ ≤ ∑ p ∈ P, 4 * (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
          sum_le_sum (fun p hp => sqrt_prime_correction_le p (hP p hp))
        _ = 4 * ∑ p ∈ P, (p : ℝ) ^ (-(3 / 2 : ℝ)) := (mul_sum _ _ _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (radicalTailSeries_summable.sum_le_tsum P (fun _ _ => rpow_nonneg (Nat.cast_nonneg _) _))
          (by norm_num)

#print axioms radicalHalfWeight_factored_bound
end Erdos970.FiniteSelberg
