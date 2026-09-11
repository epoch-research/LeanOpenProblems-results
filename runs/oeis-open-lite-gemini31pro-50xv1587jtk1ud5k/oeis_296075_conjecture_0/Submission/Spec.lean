import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
open Nat ArithmeticFunction Finset

def a (n : ℕ) : ℤ := (divisors n).sum fun d => (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)
theorem oeis_296075_conjecture_0 : ∀ n : ℕ, a n = 1 ↔ n = 1 ∨ n = 12 := sorry

def Y : ArithmeticFunction ℕ := sigma 1 * zeta

theorem Y_eq_nat (n : ℕ) (hn : n ≠ 0) : Y n = (divisors n).sum (sigma 1) := by
  change (sigma 1 * zeta) n = (divisors n).sum (sigma 1)
  rw [mul_apply, @sum_divisorsAntidiagonal ℕ _ (fun i j => sigma 1 i * zeta j) n]
  apply sum_congr rfl
  intro x hx
  have hne : n / x ≠ 0 := Nat.ne_of_gt (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.dvd_of_mem_divisors hx)) (Nat.pos_of_mem_divisors hx))
  simp [hne, zeta_apply]

theorem a_eq (n : ℕ) (hn : n ≠ 0) : a n = 2 * (sigma 1 n : ℤ) - (Y n : ℤ) := by
  unfold a
  rw [sum_sub_distrib, ← mul_sum]
  have h_sig_d : (divisors n).sum (fun d => (d : ℤ)) = (sigma 1 n : ℤ) := by
    rw [← Nat.cast_sum, sigma_one_apply]
  have h_Y : (divisors n).sum (fun d => (sigma 1 d : ℤ)) = (Y n : ℤ) := by
    rw [← Nat.cast_sum, Y_eq_nat n hn]
  rw [h_sig_d, h_Y]

theorem disproof_abstract (N : ℕ) (h_N_not_0 : N ≠ 0) (h_N_not_1 : N ≠ 1) (h_N_not_12 : N ≠ 12) 
  (h_math : 2 * (sigma 1 N : ℤ) - (Y N : ℤ) = 1) (h : ∀ n, a n = 1 ↔ n = 1 ∨ n = 12) : False := by
  have h_eval : a N = 1 ↔ N = 1 ∨ N = 12 := h N
  have h_a : a N = 1 := Eq.trans (a_eq N h_N_not_0) h_math
  have h4 : N = 1 ∨ N = 12 := h_eval.mp h_a
  cases h4 with
  | inl h_inl => exact h_N_not_1 h_inl
  | inr h_inr => exact h_N_not_12 h_inr

theorem h_math_proof (N : ℕ) (h_eq_X : sigma 1 N = 32767 * 4410 * 458010) (h_eq_Y : Y N = 65519 * 4411 * 458011) : 2 * (sigma 1 N : ℤ) - (Y N : ℤ) = 1 := by
  have h1 : 2 * (sigma 1 N : ℤ) - (Y N : ℤ) = 2 * ((32767 * 4410 * 458010 : ℕ) : ℤ) - ((65519 * 4411 * 458011 : ℕ) : ℤ) := by rw [h_eq_X, h_eq_Y]
  have h2 : 2 * ((32767 * 4410 * 458010 : ℕ) : ℤ) - ((65519 * 4411 * 458011 : ℕ) : ℤ) = 1 := by norm_num
  exact Eq.trans h1 h2

theorem map_mul_nat {f : ArithmeticFunction ℕ} (hf : f.IsMultiplicative) {m n : ℕ} (h : m.Coprime n) : f (m * n) = f m * f n :=
  hf.map_mul_of_coprime h

theorem sigma_prime_val_thm {p : ℕ} (hp : Nat.Prime p) : sigma 1 p = 1 + p := by
  rw [sigma_one_apply, Nat.Prime.divisors hp, sum_insert (by simp [hp.ne_one.symm]), sum_singleton]

theorem Y_prime_val {p : ℕ} (hp : Nat.Prime p) : Y p = p + 2 := by
  have sigma_prime_val : sigma 1 p = 1 + p := sigma_prime_val_thm hp
  rw [Y_eq_nat p hp.ne_zero, Nat.Prime.divisors hp, sum_insert (by simp [hp.ne_one.symm]), sum_singleton]
  rw [show sigma 1 1 = 1 from rfl, sigma_prime_val, ← Nat.add_assoc, Nat.add_comm (1+1) p]

theorem Y_prime_pow {p k : ℕ} (hp : Nat.Prime p) (h_pow_ne_0 : p^k ≠ 0) : Y (p^k) = ∑ j ∈ range (k + 1), sigma 1 (p ^ j) := by
  rw [Y_eq_nat (p^k) h_pow_ne_0, divisors_prime_pow hp]; exact sum_map _ _ _

theorem prime_4409 : Nat.Prime 4409 := by norm_num
theorem prime_458009 : Nat.Prime 458009 := by norm_num
theorem hX1 : Coprime (2^14 * 4409) 458009 := by norm_num
theorem hX2 : Coprime (2^14) 4409 := by norm_num

theorem eq_X : sigma 1 (2^14 * 4409 * 458009) = 32767 * 4410 * 458010 := by
  have h_step1 := map_mul_nat (@isMultiplicative_sigma 1) hX1
  have h_step2 := map_mul_nat (@isMultiplicative_sigma 1) hX2
  have h_step3 : sigma 1 ((2^14 * 4409) * 458009) = sigma 1 (2^14) * sigma 1 4409 * sigma 1 458009 := by
    rw [h_step1, h_step2]
  have sigma_prime_val1 : sigma 1 4409 = 4410 := by
    have h : sigma 1 4409 = 1 + 4409 := sigma_prime_val_thm prime_4409
    have h2 : 1 + 4409 = 4410 := by norm_num
    exact Eq.trans h h2
  have sigma_prime_val2 : sigma 1 458009 = 458010 := by
    have h : sigma 1 458009 = 1 + 458009 := sigma_prime_val_thm prime_458009
    have h2 : 1 + 458009 = 458010 := by norm_num
    exact Eq.trans h h2
  have sigma_pow2 : sigma 1 (2^14) = 32767 := by
    have h1 : sigma 1 (2^14) = ∑ k ∈ range (14 + 1), 2^k := sigma_one_apply_prime_pow Nat.prime_two
    have h2 : (∑ k ∈ range (14 + 1), 2^k) = 32767 := by norm_num
    exact Eq.trans h1 h2
  have h_step4 : sigma 1 (2^14) * sigma 1 4409 * sigma 1 458009 = 32767 * 4410 * 458010 := by
    rw [sigma_pow2, sigma_prime_val1, sigma_prime_val2]
  exact Eq.trans h_step3 h_step4

theorem eq_Y : Y (2^14 * 4409 * 458009) = 65519 * 4411 * 458011 := by
  have Y_mult : Y.IsMultiplicative := isMultiplicative_sigma.mul isMultiplicative_zeta
  have h_step1 := map_mul_nat Y_mult hX1
  have h_step2 := map_mul_nat Y_mult hX2
  have h_step3 : Y ((2^14 * 4409) * 458009) = Y (2^14) * Y 4409 * Y 458009 := by
    rw [h_step1, h_step2]
  have h_pow2_ne_0 : 2^14 ≠ 0 := by norm_num
  have hY_pow_eq : Y (2^14) = ∑ j ∈ range (14 + 1), sigma 1 (2 ^ j) := Y_prime_pow Nat.prime_two h_pow2_ne_0
  have h_sum_eq : (∑ j ∈ range (14 + 1), sigma 1 (2 ^ j)) = ∑ j ∈ range 15, ∑ k ∈ range (j + 1), 2 ^ k := by
    apply sum_congr rfl; intro x _; exact sigma_one_apply_prime_pow Nat.prime_two
  have h_sum_val : (∑ j ∈ range 15, ∑ k ∈ range (j + 1), 2 ^ k) = 65519 := by norm_num
  have hY_pow : Y (2^14) = 65519 := Eq.trans hY_pow_eq (Eq.trans h_sum_eq h_sum_val)
  have hy1 : Y 4409 = 4411 := by
    have h : Y 4409 = 4409 + 2 := Y_prime_val prime_4409
    have h2 : 4409 + 2 = 4411 := by norm_num
    exact Eq.trans h h2
  have hy2 : Y 458009 = 458011 := by
    have h : Y 458009 = 458009 + 2 := Y_prime_val prime_458009
    have h2 : 458009 + 2 = 458011 := by norm_num
    exact Eq.trans h h2
  have h_step4 : Y (2^14) * Y 4409 * Y 458009 = 65519 * 4411 * 458011 := by
    rw [hY_pow, hy1, hy2]
  exact Eq.trans h_step3 h_step4

theorem oeis_296075_conjecture_0.disproof : ¬ (type_of% @oeis_296075_conjecture_0) := by
  exact disproof_abstract (2^14 * 4409 * 458009) (by norm_num) (by norm_num) (by norm_num) (h_math_proof _ eq_X eq_Y)
