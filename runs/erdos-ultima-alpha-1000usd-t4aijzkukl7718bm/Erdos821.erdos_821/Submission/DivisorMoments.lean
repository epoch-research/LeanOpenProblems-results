import Submission.FiniteConvolution

/-!
# Divisor convolution moments

Elementary harmonic bounds for powers of the zeta arithmetic function
supply the divisor-square moment needed for Vaughan's Type II coefficient.
-/

open scoped BigOperators ArithmeticFunction.zeta ArithmeticFunction.sigma
open Finset ArithmeticFunction

namespace Erdos821.AnalyticSieve

lemma harmonic_real_nonneg (n : ℕ) : (0 : ℝ) ≤ harmonic n := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  positivity

lemma harmonic_real_mono {m n : ℕ} (h : m ≤ n) : (harmonic m : ℝ) ≤ harmonic n := by
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro d hd
    simp only [mem_Icc] at hd ⊢
    omega
  · intro d hd hdm
    positivity


lemma multiplicative_le_of_prime_powers (f g : ArithmeticFunction ℝ)
    (hf : f.IsMultiplicative) (hg : g.IsMultiplicative) (hf0 : ∀ n, 0 ≤ f n)
    (h : ∀ p k : ℕ, p.Prime → f (p ^ k) ≤ g (p ^ k)) (n : ℕ) : f n ≤ g n := by
  by_cases hn : n = 0
  · subst n
    simp
  rw [hf.multiplicative_factorization f hn, hg.multiplicative_factorization g hn]
  unfold Finsupp.prod
  apply Finset.prod_le_prod (fun p hp => hf0 _)
  intro p hp
  exact h p _ (Nat.prime_of_mem_primeFactors (by simpa only [Nat.support_factorization] using hp))

lemma sigma_zero_sq_le_convolution (n : ℕ) :
    ((σ 0 n : ℕ) : ℝ) ^ 2 ≤
      (((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) *
        ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)) n := by
  let t : ArithmeticFunction ℝ := ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ)
  have ht : t.IsMultiplicative := isMultiplicative_sigma.natCast
  have hp (p k : ℕ) (hp : p.Prime) : (t (p ^ k)) ^ 2 ≤ (t * t) (p ^ k) := by
    change ((σ 0 (p ^ k) : ℕ) : ℝ) ^ 2 ≤ _
    rw [sigma_zero_apply_prime_pow hp, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => t a * t b),
      Nat.sum_divisors_prime_pow hp]
    calc
      ((k + 1 : ℕ) : ℝ) ^ 2 = ∑ j ∈ range (k + 1), ((k + 1 : ℕ) : ℝ) := by simp; ring
      _ ≤ ∑ j ∈ range (k + 1), t (p ^ j) * t (p ^ k / p ^ j) := by
        apply Finset.sum_le_sum
        intro j hj
        have hjk : j ≤ k := by have := mem_range.mp hj; omega
        simp only [t, ArithmeticFunction.natCoe_apply, Nat.pow_div hjk hp.pos,
          sigma_zero_apply_prime_pow hp, Nat.cast_add, Nat.cast_one, Nat.cast_sub hjk]
        have hjk' : (j : ℝ) ≤ k := by exact_mod_cast hjk
        nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) j) (sub_nonneg.mpr hjk')]
  have h := multiplicative_le_of_prime_powers (t.ppow 2) (t * t) ht.ppow (ht.mul ht)
    (fun m => by rw [ppow_apply (by norm_num : 0 < 2)]; positivity)
    (fun p k hp' => by simpa only [ppow_apply (by norm_num : 0 < 2)] using hp p k hp') n
  simpa only [ppow_apply (by norm_num : 0 < 2), t, ArithmeticFunction.natCoe_apply] using h

lemma divisor_card_sq_le_zeta_four (n : ℕ) :
    (n.divisors.card : ℝ) ^ 2 ≤ ((ζ : ArithmeticFunction ℝ) ^ 4) n := by
  have hτ : (ζ : ArithmeticFunction ℕ) * ζ = σ 0 := by
    simpa only [pow_zero_eq_zeta] using (zeta_mul_pow_eq_sigma (k := 0))
  have hτ' : ((σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) = (ζ : ArithmeticFunction ℝ) ^ 2 := by
    rw [← hτ, natCoe_mul, pow_two]
  have h := sigma_zero_sq_le_convolution n
  rw [sigma_zero_apply, hτ', ← pow_add] at h
  exact h

/-- The summatory (k+1)-fold divisor convolution is at most N*H_N^k. -/
lemma sum_zeta_pow_le_harmonic (k N : ℕ) :
    (∑ n ∈ Icc 1 N, ((ζ : ArithmeticFunction ℝ) ^ (k + 1)) n) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  induction k generalizing N with
  | zero =>
    simp only [zero_add, pow_one, pow_zero, mul_one]
    calc
      _ = ∑ n ∈ Icc 1 N, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro n hn
        have hn0 : n ≠ 0 := by have := mem_Icc.mp hn; omega
        simp only [natCoe_apply, zeta_apply_ne hn0, Nat.cast_one]
      _ ≤ (N : ℝ) := by simp
  | succ k ih =>
    rw [pow_succ', sum_convolution_Icc]
    calc
      _ = ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 (N / m), ((ζ : ArithmeticFunction ℝ) ^ (k + 1)) n := by
        apply Finset.sum_congr rfl
        intro m hm
        have hm0 : m ≠ 0 := by have := mem_Icc.mp hm; omega
        simp only [natCoe_apply, zeta_apply_ne hm0, Nat.cast_one, one_mul]
      _ ≤ ∑ m ∈ Icc 1 N, (N : ℝ) / m * (harmonic N : ℝ) ^ k := by
        apply Finset.sum_le_sum
        intro m hm
        apply (ih (N / m)).trans
        exact mul_le_mul Nat.cast_div_le
          (pow_le_pow_left₀ (harmonic_real_nonneg _) (harmonic_real_mono (Nat.div_le_self N m)) k)
          (pow_nonneg (harmonic_real_nonneg _) _) (by positivity)
      _ = (N : ℝ) * (harmonic N : ℝ) ^ (k + 1) := by
        rw [pow_succ, harmonic_eq_sum_Icc]
        simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m hm
        ring

/-- An elementary divisor-square moment bound with the correct logarithmic order. -/
theorem sum_divisor_card_sq_le (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2) ≤ (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  exact (Finset.sum_le_sum (fun n hn => divisor_card_sq_le_zeta_four n)).trans
    (sum_zeta_pow_le_harmonic 3 N)

theorem sum_divisor_card_sq_le_log (N : ℕ) :
    (∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ 2) ≤ (N : ℝ) * (1 + Real.log N) ^ 3 := by
  apply (sum_divisor_card_sq_le N).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (harmonic_real_nonneg N) (harmonic_le_one_add_log N) 3) (Nat.cast_nonneg N)

lemma sum_vaughanTypeII_sq_le (V N : ℕ) :
    (∑ n ∈ Icc 1 N, (vaughanTypeII V n) ^ 2) ≤ (N : ℝ) * (1 + Real.log N) ^ 3 := by
  apply le_trans _ (sum_divisor_card_sq_le_log N)
  apply Finset.sum_le_sum
  intro n hn
  have h := abs_vaughanTypeII_le V n
  nlinarith [sq_abs (vaughanTypeII V n), abs_nonneg (vaughanTypeII V n),
    Nat.cast_nonneg (α := ℝ) n.divisors.card]

end Erdos821.AnalyticSieve
