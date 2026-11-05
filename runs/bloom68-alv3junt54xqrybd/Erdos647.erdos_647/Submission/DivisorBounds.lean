import FormalConjecturesUtil

/-!
# An explicit sixth-power bound for the divisor-counting function

This file is independent of `Submission.Spec`.  In particular, none of its proofs
uses the conjecture or the proposed disproof in that file.

For a prime `p < 64` the coefficient is the exact rational maximum of
`(e + 1)^6 / p^e`.  Using rational coefficients avoids the loss from rounding
all eighteen coefficients up to integers.  Their product is less than `139^6`,
so we obtain both the stronger bound with `139` and the requested bound with `200`.

The local estimates are proved by induction, after checking finitely many
exponents with `norm_num`.  All computations produce ordinary kernel-checked proofs.
-/

namespace DivisorBounds

open scoped ArithmeticFunction.sigma
open Finset

/-- The ratio `(e + 2)/(e + 1)` decreases with `e`, in a division-free form. -/
private theorem sixth_step_of_cutoff {p E e : ℕ} (hEe : E ≤ e)
    (hE : (E + 2) ^ 6 ≤ p * (E + 1) ^ 6) :
    (e + 2) ^ 6 ≤ p * (e + 1) ^ 6 := by
  have hcross : (E + 1) * (e + 2) ≤ (E + 2) * (e + 1) := by
    nlinarith
  have hpow := Nat.pow_le_pow_left hcross 6
  rw [mul_pow, mul_pow] at hpow
  apply Nat.le_of_mul_le_mul_left (c := (E + 1) ^ 6) _ (by positivity)
  calc
    (E + 1) ^ 6 * (e + 2) ^ 6 ≤ (E + 2) ^ 6 * (e + 1) ^ 6 := hpow
    _ ≤ (p * (E + 1) ^ 6) * (e + 1) ^ 6 := Nat.mul_le_mul_right _ hE
    _ = (E + 1) ^ 6 * (p * (e + 1) ^ 6) := by ring

/-- A finite check and a decreasing-ratio check imply an estimate for every exponent.
The factor `d` allows us to keep the rational coefficient `c / d` exact. -/
private theorem sixth_bound_of_cutoff {p c d E : ℕ}
    (hsmall : ∀ e : ℕ, e ≤ E → d * (e + 1) ^ 6 ≤ c * p ^ e)
    (hstep : (E + 2) ^ 6 ≤ p * (E + 1) ^ 6) (e : ℕ) :
    d * (e + 1) ^ 6 ≤ c * p ^ e := by
  induction e with
  | zero => exact hsmall 0 (Nat.zero_le _)
  | succ e ih =>
    by_cases he : e + 1 ≤ E
    · exact hsmall (e + 1) he
    · have hEe : E ≤ e := by omega
      calc
        d * (e + 1 + 1) ^ 6 ≤ d * (p * (e + 1) ^ 6) := by
          apply Nat.mul_le_mul_left
          simpa only [Nat.add_assoc] using sixth_step_of_cutoff hEe hstep
        _ = p * (d * (e + 1) ^ 6) := by ring
        _ ≤ p * (c * p ^ e) := Nat.mul_le_mul_left p ih
        _ = c * p ^ (e + 1) := by rw [pow_succ]; ring

/-- Rational version of the local estimate, still proved from inequalities in `ℕ`. -/
private theorem sixth_ratio_bound {p E : ℕ} (hp : 0 < p)
    (hsmall : ∀ e : ℕ, e ≤ E → p ^ E * (e + 1) ^ 6 ≤ (E + 1) ^ 6 * p ^ e)
    (hstep : (E + 2) ^ 6 ≤ p * (E + 1) ^ 6) (e : ℕ) :
    ((e + 1 : ℕ) : ℚ) ^ 6 ≤
      (((E + 1 : ℕ) : ℚ) ^ 6 / (p : ℚ) ^ E) * (p : ℚ) ^ e := by
  have hnat := sixth_bound_of_cutoff hsmall hstep e
  have hrat : (p : ℚ) ^ E * ((e + 1 : ℕ) : ℚ) ^ 6 ≤
      ((E + 1 : ℕ) : ℚ) ^ 6 * (p : ℚ) ^ e := by
    exact_mod_cast hnat
  have hpos : 0 < (p : ℚ) ^ E := pow_pos (by exact_mod_cast hp) E
  rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
  simpa only [mul_comm] using hrat

private def smallPrimes : Finset ℕ :=
  {2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61}

private def criticalExponent : ℕ → ℕ
  | 2 => 8
  | 3 => 4
  | 5 => 3
  | 7 => 2
  | 11 => 2
  | _ => 1

private def localConstant (p : ℕ) : ℚ :=
  if p ∈ smallPrimes then
    ((criticalExponent p + 1 : ℕ) : ℚ) ^ 6 / (p : ℚ) ^ criticalExponent p
  else 1

private theorem small_prime_lt {p : ℕ} (hp : p ∈ smallPrimes) : p < 64 := by
  simp only [smallPrimes, mem_insert, mem_singleton] at hp
  omega

private theorem prime_lt_mem {p : ℕ} (hp : p.Prime) (h64 : p < 64) :
    p ∈ smallPrimes := by
  have h2 := hp.two_le
  interval_cases p <;> norm_num at hp <;> decide

private theorem one_le_localConstant (p : ℕ) : 1 ≤ localConstant p := by
  by_cases hp : p ∈ smallPrimes
  · rw [localConstant, if_pos hp]
    simp only [smallPrimes, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [criticalExponent]
  · simp [localConstant, hp]

private theorem small_prime_sixth_bound {p : ℕ} (hp : p ∈ smallPrimes) (e : ℕ) :
    ((e + 1 : ℕ) : ℚ) ^ 6 ≤ localConstant p * (p : ℚ) ^ e := by
  have hp0 : 0 < p := by
    simp only [smallPrimes, mem_insert, mem_singleton] at hp
    omega
  rw [localConstant, if_pos hp]
  apply sixth_ratio_bound hp0
  · intro i hi
    simp only [smallPrimes, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      norm_num [criticalExponent] at hi ⊢
      interval_cases i <;> norm_num
  · simp only [smallPrimes, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [criticalExponent]

/-- For `p ≥ 64` no coefficient is needed. -/
theorem sixth_bound_of_large_base {p : ℕ} (hp : 64 ≤ p) (e : ℕ) :
    (e + 1) ^ 6 ≤ p ^ e := by
  have h : 1 * (e + 1) ^ 6 ≤ 1 * p ^ e := by
    apply sixth_bound_of_cutoff (E := 0)
    · intro i hi
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst i
      norm_num
    · simpa using hp
  simpa using h

private theorem prime_sixth_bound {p : ℕ} (hp : p.Prime) (e : ℕ) :
    ((e + 1 : ℕ) : ℚ) ^ 6 ≤ localConstant p * (p : ℚ) ^ e := by
  by_cases h64 : 64 ≤ p
  · have hnot : p ∉ smallPrimes := by
      intro hmem
      have := small_prime_lt hmem
      omega
    rw [localConstant, if_neg hnot, one_mul]
    exact_mod_cast sixth_bound_of_large_base h64 e
  · exact small_prime_sixth_bound (prime_lt_mem hp (by omega)) e

private theorem smallPrimes_product :
    (∏ p ∈ smallPrimes, localConstant p) =
      (2107631844899214418882499117580288000 : ℚ) / 301040178822477892190393 := by
  calc
    (∏ p ∈ smallPrimes, localConstant p) =
        ∏ p ∈ smallPrimes,
          ((criticalExponent p + 1 : ℕ) : ℚ) ^ 6 / (p : ℚ) ^ criticalExponent p := by
      apply prod_congr rfl
      intro p hp
      simp only [localConstant, if_pos hp]
    _ = _ := by norm_num [smallPrimes, criticalExponent, -Finset.insert_eq_of_mem]

private theorem smallPrimes_product_le :
    (∏ p ∈ smallPrimes, localConstant p) ≤ (139 : ℚ) ^ 6 := by
  rw [smallPrimes_product]
  norm_num

private theorem localConstant_product_le (s : Finset ℕ) :
    (∏ p ∈ s, localConstant p) ≤ (139 : ℚ) ^ 6 := by
  have hprod : (∏ p ∈ s ∩ smallPrimes, localConstant p) =
      ∏ p ∈ s, localConstant p := by
    apply prod_subset inter_subset_left
    intro p hp hnot
    have hnotSmall : p ∉ smallPrimes := by
      intro hmem
      exact hnot (mem_inter.mpr ⟨hp, hmem⟩)
    simp [localConstant, hnotSmall]
  calc
    (∏ p ∈ s, localConstant p) = ∏ p ∈ smallPrimes ∩ s, localConstant p := by
      rw [← hprod, inter_comm]
    _ ≤ (∏ p ∈ smallPrimes ∩ s, localConstant p) *
        ∏ p ∈ smallPrimes \ s, localConstant p :=
      le_mul_of_one_le_right
        (prod_nonneg fun p _ => le_trans (by norm_num) (one_le_localConstant p))
        (Finset.one_le_prod _ one_le_localConstant)
    _ = ∏ p ∈ smallPrimes, localConstant p :=
      prod_inter_mul_prod_diff smallPrimes s localConstant
    _ ≤ (139 : ℚ) ^ 6 := smallPrimes_product_le

/-- An unconditional explicit sixth-power bound for the divisor-counting function.
It includes `n = 0`, for which Mathlib defines `σ 0 0 = 0`. -/
theorem sigma_zero_pow_six_le_139 (n : ℕ) : (σ 0 n) ^ 6 ≤ 139 ^ 6 * n := by
  by_cases hn : n = 0
  · subst n
    norm_num [ArithmeticFunction.sigma_zero_apply]
  have hcard : σ 0 n = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
    rw [ArithmeticFunction.sigma_zero_apply, Nat.card_divisors hn]
  have hnprod : (∏ p ∈ n.primeFactors, (p : ℚ) ^ n.factorization p) = (n : ℚ) := by
    have hnat : (∏ p ∈ n.primeFactors, p ^ n.factorization p) = n := by
      simpa only [Finsupp.prod, Nat.support_factorization] using
        Nat.factorization_prod_pow_eq_self hn
    exact_mod_cast hnat
  have hrat : ((σ 0 n : ℕ) : ℚ) ^ 6 ≤ (139 : ℚ) ^ 6 * (n : ℚ) := by
    calc
      ((σ 0 n : ℕ) : ℚ) ^ 6 =
          ∏ p ∈ n.primeFactors, ((n.factorization p + 1 : ℕ) : ℚ) ^ 6 := by
        rw [hcard, Nat.cast_prod, prod_pow]
      _ ≤ ∏ p ∈ n.primeFactors, localConstant p * (p : ℚ) ^ n.factorization p :=
        prod_le_prod (fun p _ => by positivity)
          (fun p hp => prime_sixth_bound (Nat.prime_of_mem_primeFactors hp) _)
      _ = (∏ p ∈ n.primeFactors, localConstant p) * (n : ℚ) := by
        rw [prod_mul_distrib, hnprod]
      _ ≤ (139 : ℚ) ^ 6 * (n : ℚ) :=
        mul_le_mul_of_nonneg_right (localConstant_product_le _) (Nat.cast_nonneg n)
  exact_mod_cast hrat

/-- The requested bound, with the constant `200`. -/
theorem sigma_zero_pow_six_le (n : ℕ) : (σ 0 n) ^ 6 ≤ 200 ^ 6 * n := by
  exact (sigma_zero_pow_six_le_139 n).trans (Nat.mul_le_mul_right n (by norm_num))

/-- The sixth-power bound gives a uniform divisor-count bound on `[0,n]`.
The strict comparison with `(B + 1)^6` is important: it implies `σ 0 m ≤ B`. -/
theorem sigma_zero_le_of_size {m n B : ℕ} (hm : m ≤ n)
    (hsize : 200 ^ 6 * n < (B + 1) ^ 6) : σ 0 m ≤ B := by
  have hpow : (σ 0 m) ^ 6 < (B + 1) ^ 6 :=
    lt_of_le_of_lt
      ((sigma_zero_pow_six_le m).trans (Nat.mul_le_mul_left (200 ^ 6) hm)) hsize
  have hlt : σ 0 m < B + 1 := (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mp hpow
  omega

/-- Given a uniform bound `σ 0 m ≤ B` for `m < n`, only the gaps
`1 ≤ k ≤ B - 3` need checking.  The case `m = 0` is automatic, and a larger
gap has `k + 2 ≥ B`.  No lower bound on `B` or `n` is required. -/
theorem tail_reduction_of_uniform_bound {n B : ℕ}
    (hcount : ∀ m : ℕ, m < n → σ 0 m ≤ B)
    (hwindow : ∀ k : ℕ, 0 < k → k ≤ B - 3 → k < n → σ 0 (n - k) ≤ k + 2) :
    ∀ m : ℕ, m < n → m + σ 0 m ≤ n + 2 := by
  intro m hm
  by_cases hm0 : m = 0
  · subst m
    simp
  have hgap0 : 0 < n - m := Nat.sub_pos_of_lt hm
  have hgapn : n - m < n := by omega
  have hsum : m + (n - m) = n := by omega
  by_cases hgap : n - m ≤ B - 3
  · have hτ := hwindow (n - m) hgap0 hgap hgapn
    rw [Nat.sub_sub_self hm.le] at hτ
    omega
  · have hτ := hcount m hm
    omega

/-- A tail-window certificate and the explicit size comparison imply the bound
for **every** `m < n`, not just the numbers in the checked tail window. -/
theorem tail_reduction {n B : ℕ}
    (hwindow : ∀ k : ℕ, 0 < k → k ≤ B - 3 → k < n → σ 0 (n - k) ≤ k + 2)
    (hsize : 200 ^ 6 * n < (B + 1) ^ 6) :
    ∀ m : ℕ, m < n → m + σ 0 m ≤ n + 2 := by
  apply tail_reduction_of_uniform_bound _ hwindow
  intro m hm
  exact sigma_zero_le_of_size hm.le hsize

/-- The same tail reduction using the stronger constant `139`. -/
theorem tail_reduction_139 {n B : ℕ}
    (hwindow : ∀ k : ℕ, 0 < k → k ≤ B - 3 → k < n → σ 0 (n - k) ≤ k + 2)
    (hsize : 139 ^ 6 * n < (B + 1) ^ 6) :
    ∀ m : ℕ, m < n → m + σ 0 m ≤ n + 2 := by
  apply tail_reduction_of_uniform_bound _ hwindow
  intro m hm
  have hpow : (σ 0 m) ^ 6 < (B + 1) ^ 6 :=
    lt_of_le_of_lt
      ((sigma_zero_pow_six_le_139 m).trans (Nat.mul_le_mul_left (139 ^ 6) hm.le)) hsize
  have hlt : σ 0 m < B + 1 := (Nat.pow_lt_pow_iff_left (by decide : 6 ≠ 0)).mp hpow
  omega

/-- The `Fin n` supremum form used in Erdős problem 647.  This also covers `n = 0`. -/
theorem tail_reduction_iSup {n B : ℕ}
    (hwindow : ∀ k : ℕ, 0 < k → k ≤ B - 3 → k < n → σ 0 (n - k) ≤ k + 2)
    (hsize : 200 ^ 6 * n < (B + 1) ^ 6) :
    (⨆ m : Fin n, (m : ℕ) + σ 0 (m : ℕ)) ≤ n + 2 := by
  by_cases hn : 0 < n
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
    apply ciSup_le
    intro m
    exact tail_reduction hwindow hsize m.val m.isLt
  · have hn0 : n = 0 := by omega
    subst n
    simp

end DivisorBounds
