import FormalConjectures.Util.ProblemImports

open Polynomial

/--
A070518: Value of $n$-th cyclotomic polynomial at $n$.
$$ a(n) = \Phi_n(n) $$
-/
noncomputable def a (n : ℕ) : ℕ :=
  (Polynomial.eval (Int.ofNat n) (cyclotomic n ℤ)).natAbs

-- Numerical fact (checked by kernel computation): `283411² ∣ 28341^28341 - 1`.
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
private lemma modfact1 : (283411 ^ 2 : ℕ) ∣ 28341 ^ 28341 - 1 :=
  Nat.dvd_of_mod_eq_zero (by decide)

-- For every proper divisor `d` of `28341`, the prime `283411` does not divide
-- `28341^d - 1` (equivalently, the multiplicative order of `28341` mod `283411` is
-- exactly `28341`).
set_option maxRecDepth 100000 in
set_option exponentiation.threshold 100000 in
private lemma modfact2 :
    ∀ d ∈ (28341 : ℕ).properDivisors, ¬ (283411 : ℤ) ∣ (28341 : ℤ) ^ d - 1 := by
  have hset : (28341 : ℕ).properDivisors
      = {1, 3, 9, 47, 67, 141, 201, 423, 603, 3149, 9447} := by decide
  intro d hd hdvd'
  have h2 : (283411 : ℕ) ∣ 28341 ^ d - 1 := by
    have hc : (28341 : ℤ) ^ d - 1 = ((28341 ^ d - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one]
    rw [hc] at hdvd'; exact_mod_cast hdvd'
  have h3 : (28341 ^ d - 1) % 283411 = 0 := Nat.dvd_iff_mod_eq_zero.mp h2
  clear hdvd' h2
  rw [hset] at hd
  fin_cases hd <;> revert h3 <;> decide

set_option maxRecDepth 100000 in
/--
A070518 a(28341) is divisible by 283411^2. What is the next n such that a(n) is not squarefree? - _Jianing Song_, Nov 01 2024
-/
theorem oeis_70518_conjecture_0 :
  (283411 : ℕ) ^ 2 ∣ a 28341 :=
by
  -- `283411` is prime (as an integer).
  have hp_int : Prime (283411 : ℤ) := Nat.prime_iff_prime_int.mp (by norm_num)
  -- The factorisation `∏_{d ∣ n} Φ_d(n) = n^n - 1`, split off the top divisor `n = 28341`.
  have H : Polynomial.eval (28341 : ℤ) (cyclotomic 28341 ℤ) *
      (∏ i ∈ (28341 : ℕ).properDivisors, Polynomial.eval (28341 : ℤ) (cyclotomic i ℤ))
      = (28341 : ℤ) ^ 28341 - 1 := by
    have h0 := prod_cyclotomic_eq_X_pow_sub_one (show 0 < 28341 by norm_num) ℤ
    have h1 := congrArg (Polynomial.eval (28341 : ℤ)) h0
    rw [eval_prod] at h1
    rw [← Nat.cons_self_properDivisors (show (28341 : ℕ) ≠ 0 by norm_num), Finset.prod_cons] at h1
    rw [h1]; simp [eval_sub, eval_pow, eval_X, eval_one]
  -- `283411² ∣ 28341^28341 - 1`, lifted from `modfact1`.
  have hdvd : (283411 : ℤ) ^ 2 ∣ (28341 : ℤ) ^ 28341 - 1 := by
    have hc : (28341 : ℤ) ^ 28341 - 1 = ((28341 ^ 28341 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (Nat.one_le_pow _ _ (by norm_num)), Nat.cast_pow, Nat.cast_ofNat,
        Nat.cast_one]
    rw [hc]; exact_mod_cast modfact1
  -- `283411` divides none of the other cyclotomic values, so it is coprime to their product.
  have hnotdvd : ¬ (283411 : ℤ) ∣
      ∏ i ∈ (28341 : ℕ).properDivisors, Polynomial.eval (28341 : ℤ) (cyclotomic i ℤ) := by
    apply Prime.not_dvd_finset_prod hp_int
    intro d hd hpd
    have hfd : Polynomial.eval (28341 : ℤ) (cyclotomic d ℤ) ∣ (28341 : ℤ) ^ d - 1 := by
      have hh : Polynomial.eval (28341 : ℤ) (cyclotomic d ℤ)
          ∣ Polynomial.eval (28341 : ℤ) (X ^ d - 1) :=
        eval_dvd (cyclotomic.dvd_X_pow_sub_one d ℤ)
      simpa [eval_sub, eval_pow, eval_X, eval_one] using hh
    exact modfact2 d hd (hpd.trans hfd)
  have hcop : IsCoprime ((283411 : ℤ) ^ 2)
      (∏ i ∈ (28341 : ℕ).properDivisors, Polynomial.eval (28341 : ℤ) (cyclotomic i ℤ)) :=
    ((Prime.coprime_iff_not_dvd hp_int).mpr hnotdvd).pow_left
  -- Since `283411²` divides the product and is coprime to the "other" factor, it divides `Φ_n(n)`.
  have hCdvd : (283411 : ℤ) ^ 2 ∣ Polynomial.eval (28341 : ℤ) (cyclotomic 28341 ℤ) := by
    apply hcop.dvd_of_dvd_mul_right; rw [H]; exact hdvd
  -- Transfer back to the natural-number absolute value used in the definition of `a`.
  show (283411 : ℕ) ^ 2 ∣ (Polynomial.eval (Int.ofNat 28341) (cyclotomic 28341 ℤ)).natAbs
  have e : Int.ofNat 28341 = (28341 : ℤ) := rfl
  rw [e]
  have := Int.natAbs_dvd_natAbs.mpr hCdvd
  simpa using this
