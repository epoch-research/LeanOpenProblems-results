import FormalConjecturesUtil

/-! Elementary mean-square estimates for divisor coefficients. -/
namespace Erdos972DivisorEnergy
open Finset ArithmeticFunction
open scoped ArithmeticFunction ArithmeticFunction.sigma ArithmeticFunction.zeta

lemma tau_square_le_tau_convolution_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (σ 0 (p ^ k)) ^ 2 ≤ (σ 0 * σ 0) (p ^ k) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => σ 0 a * σ 0 b),
    Nat.sum_divisors_prime_pow hp, sigma_zero_apply_prime_pow hp]
  calc
    _ = ∑ i ∈ range (k + 1), (k + 1) := by simp [pow_two]
    _ ≤ _ := by
      apply sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.le_of_lt_succ (mem_range.mp hi)
      rw [Nat.pow_div hik hp.pos, sigma_zero_apply_prime_pow hp,
        sigma_zero_apply_prime_pow hp]
      have hki := Nat.sub_add_cancel hik
      nlinarith

/-- The pointwise inequality `τ(n)² ≤ (τ * τ)(n)`. -/
theorem tau_square_le_tau_convolution (n : ℕ) :
    (σ 0 n) ^ 2 ≤ (σ 0 * σ 0) n := by
  by_cases hn : n = 0
  · simp [hn]
  have ht := isMultiplicative_sigma (k := 0)
  rw [ht.multiplicative_factorization _ hn,
    (ht.mul ht).multiplicative_factorization _ hn]
  unfold Finsupp.prod
  rw [← prod_pow]
  apply prod_le_prod (fun _ _ => Nat.zero_le _)
  intro p hp
  apply tau_square_le_tau_convolution_prime_pow
  exact Nat.prime_of_mem_primeFactors (by simpa only [n.support_factorization] using hp)

/-- Reindex a divisor convolution as a hyperbolically truncated rectangle. -/
lemma sum_divisorsAntidiagonal_eq_sum_box {E : Type*} [AddCommMonoid E]
    (F : ℕ → ℕ → E) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ ab ∈ n.divisorsAntidiagonal, F ab.1 ab.2) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 N, if a * b ≤ N then F a b else 0 := by
  classical
  calc
    _ = ∑ n ∈ Ioc 0 N, ∑ ab ∈ Ioc 0 N ×ˢ Ioc 0 N,
        if ab.1 * ab.2 = n then F ab.1 ab.2 else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [Nat.divisorsAntidiagonal_eq_prod_filter_of_le
        (Nat.ne_of_gt (mem_Ioc.mp hn).1) (mem_Ioc.mp hn).2, sum_filter]
    _ = ∑ ab ∈ Ioc 0 N ×ˢ Ioc 0 N, ∑ n ∈ Ioc 0 N,
        if ab.1 * ab.2 = n then F ab.1 ab.2 else 0 := sum_comm
    _ = _ := by
      rw [sum_product]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      have hab : 0 < a * b := Nat.mul_pos (mem_Ioc.mp ha).1 (mem_Ioc.mp hb).1
      simp only [sum_ite_eq, mem_Ioc, hab, true_and]

lemma sum_divisorsAntidiagonal_eq_sum_hyperbola {E : Type*} [AddCommMonoid E]
    (F : ℕ → ℕ → E) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, ∑ ab ∈ n.divisorsAntidiagonal, F ab.1 ab.2) =
      ∑ a ∈ Ioc 0 N, ∑ b ∈ Ioc 0 (N / a), F a b := by
  classical
  rw [sum_divisorsAntidiagonal_eq_sum_box]
  apply sum_congr rfl
  intro a ha
  rw [← sum_filter]
  congr 1
  ext b
  simp only [mem_filter, mem_Ioc]
  have ha0 : 0 < a := (mem_Ioc.mp ha).1
  constructor
  · rintro ⟨⟨hb0, hbN⟩, hab⟩
    exact ⟨hb0, (Nat.le_div_iff_mul_le ha0).mpr (by simpa [mul_comm] using hab)⟩
  · rintro ⟨hb0, hba⟩
    refine ⟨⟨hb0, hba.trans (Nat.div_le_self N a)⟩, ?_⟩
    simpa [mul_comm] using (Nat.le_div_iff_mul_le ha0).mp hba

/-- The truncated reciprocal sum of a nonnegative Dirichlet convolution is at
most the product of the truncated reciprocal sums. -/
lemma reciprocal_sum_convolution_le (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (f * g) n / n) ≤
      (∑ a ∈ Ioc 0 N, f a / a) * ∑ b ∈ Ioc 0 N, g b / b := by
  have he (n : ℕ) : (f * g) n / n =
      ∑ ab ∈ n.divisorsAntidiagonal, (f ab.1 / ab.1) * (g ab.2 / ab.2) := by
    rw [ArithmeticFunction.mul_apply, sum_div]
    apply sum_congr rfl
    intro ab hab
    rw [← (Nat.mem_divisorsAntidiagonal.mp hab).1, Nat.cast_mul, mul_div_mul_comm]
  simp_rw [he]
  rw [sum_divisorsAntidiagonal_eq_sum_box (fun a b => (f a / a) * (g b / b)) N,
    sum_mul_sum]
  apply sum_le_sum
  intro a ha
  apply sum_le_sum
  intro b hb
  split_ifs
  · rfl
  · exact mul_nonneg (div_nonneg (hf a) (Nat.cast_nonneg _))
      (div_nonneg (hg b) (Nat.cast_nonneg _))

lemma sum_convolution_zeta_le (f : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (f * ζ) n) ≤
      (N : ℝ) * ∑ a ∈ Ioc 0 N, f a / a := by
  simp_rw [ArithmeticFunction.mul_apply]
  rw [sum_divisorsAntidiagonal_eq_sum_hyperbola (fun a b => f a * (ζ : ArithmeticFunction ℝ) b) N,
    mul_sum]
  apply sum_le_sum
  intro a ha
  have he : (∑ b ∈ Ioc 0 (N / a), f a * (ζ : ArithmeticFunction ℝ) b) =
      (N / a : ℕ) * f a := by
    have hb (b : ℕ) (hb : b ∈ Ioc 0 (N / a)) : (ζ : ArithmeticFunction ℝ) b = 1 := by
      simp only [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hb).1), Nat.cast_one]
    simp only [sum_congr rfl (fun b hb' => congrArg (f a * ·) (hb b hb')),
      mul_one, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul]
  rw [he]
  have hdiv : ((N / a : ℕ) : ℝ) ≤ (N : ℝ) / a := by
    exact (le_div_iff₀ (Nat.cast_pos.mpr (mem_Ioc.mp ha).1)).mpr (by
      exact_mod_cast Nat.div_mul_le_self N a)
  calc
    _ ≤ ((N : ℝ) / a) * f a := mul_le_mul_of_nonneg_right hdiv (hf a)
    _ = _ := by ring

lemma convolution_nonneg (f g : ArithmeticFunction ℝ)
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) :
    0 ≤ (f * g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg (fun ab hab => mul_nonneg (hf ab.1) (hg ab.2))

lemma zeta_pow_nonneg (k n : ℕ) : 0 ≤ ((ζ : ArithmeticFunction ℝ) ^ k) n := by
  induction k generalizing n with
  | zero => simp only [pow_zero, one_apply]; split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    exact convolution_nonneg _ _ ih
      (fun n => Nat.cast_nonneg _) n

lemma reciprocal_sum_zeta (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) n / n) = (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum,
    show Icc 1 N = Ioc 0 N from Icc_add_one_left_eq_Ioc 0 N]
  apply sum_congr rfl
  intro n hn
  simp [natCoe_apply, zeta_apply_ne (Nat.ne_of_gt (mem_Ioc.mp hn).1)]

lemma harmonic_real_nonneg (N : ℕ) : 0 ≤ (harmonic N : ℝ) := by
  rw [harmonic_eq_sum_Icc, Rat.cast_sum]
  exact sum_nonneg (fun n hn => by positivity)

lemma reciprocal_sum_zeta_pow_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ : ArithmeticFunction ℝ) ^ k) n / n) ≤
      (harmonic N : ℝ) ^ k := by
  induction k with
  | zero =>
    simp only [pow_zero, one_apply, ite_div, zero_div, sum_ite_eq']
    split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ]
    calc
      _ ≤ (∑ n ∈ Ioc 0 N, ((ζ : ArithmeticFunction ℝ) ^ k) n / n) *
          ∑ n ∈ Ioc 0 N, (ζ : ArithmeticFunction ℝ) n / n :=
        reciprocal_sum_convolution_le _ _ (zeta_pow_nonneg k) (fun n => Nat.cast_nonneg _) N
      _ = (∑ n ∈ Ioc 0 N, ((ζ : ArithmeticFunction ℝ) ^ k) n / n) *
          (harmonic N : ℝ) := by rw [reciprocal_sum_zeta]
      _ ≤ (harmonic N : ℝ) ^ k * harmonic N :=
        mul_le_mul_of_nonneg_right ih (harmonic_real_nonneg N)
      _ = _ := (pow_succ _ _).symm

lemma sum_zeta_pow_le (k N : ℕ) :
    (∑ n ∈ Ioc 0 N, ((ζ : ArithmeticFunction ℝ) ^ (k + 1)) n) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ k := by
  rw [pow_succ]
  exact (sum_convolution_zeta_le _ (zeta_pow_nonneg k) N).trans
    (mul_le_mul_of_nonneg_left (reciprocal_sum_zeta_pow_le k N) (Nat.cast_nonneg _))

lemma card_divisors_square_le_zeta_four (n : ℕ) :
    (n.divisors.card : ℝ) ^ 2 ≤ ((ζ : ArithmeticFunction ℝ) ^ 4) n := by
  have he : ((σ 0 * σ 0 : ArithmeticFunction ℕ) : ArithmeticFunction ℝ) =
      (ζ : ArithmeticFunction ℝ) ^ 4 := by
    rw [← zeta_mul_pow_eq_sigma (k := 0), pow_zero_eq_zeta]
    simp only [natCoe_mul]
    ring
  rw [← he, natCoe_apply]
  exact_mod_cast (show n.divisors.card ^ 2 ≤ (σ 0 * σ 0) n by
    simpa only [sigma_zero_apply] using tau_square_le_tau_convolution n)

/-- An elementary mean-square bound for the divisor function. -/
theorem sum_card_divisors_square_le_harmonic (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (harmonic N : ℝ) ^ 3 := by
  calc
    _ ≤ ∑ n ∈ Ioc 0 N, ((ζ : ArithmeticFunction ℝ) ^ 4) n :=
      sum_le_sum (fun n hn => card_divisors_square_le_zeta_four n)
    _ ≤ _ := sum_zeta_pow_le 3 N

/-- The standard logarithmic form, avoiding a pointwise `n^ε` divisor bound. -/
theorem sum_card_divisors_square_le_log (N : ℕ) :
    (∑ n ∈ Ioc 0 N, (n.divisors.card : ℝ) ^ 2) ≤
      (N : ℝ) * (1 + Real.log N) ^ 3 := by
  apply (sum_card_divisors_square_le_harmonic N).trans
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (harmonic_real_nonneg N) (harmonic_le_one_add_log N) 3)
    (Nat.cast_nonneg _)

#print axioms sum_card_divisors_square_le_log
#print axioms sum_zeta_pow_le
#print axioms reciprocal_sum_convolution_le
#print axioms sum_convolution_zeta_le
#print axioms tau_square_le_tau_convolution
end Erdos972DivisorEnergy
