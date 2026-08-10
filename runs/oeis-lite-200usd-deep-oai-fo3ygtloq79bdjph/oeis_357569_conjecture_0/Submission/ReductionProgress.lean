import FormalConjectures.Util.ProblemImports
open Nat

/-- Same sequence as in `Spec.lean`, copied to keep this progress file independent. -/
def a (n : ℕ) : ℤ :=
  (Int.ofNat ((3 * n).choose n)) ^ 2 - (27 : ℤ) * Int.ofNat ((2 * n).choose n)

/-- Algebraic reduction of OEIS 357569 step to a single binomial-difference congruence. -/
lemma oeis_357569_step_of_binomial_square_linear_congruence
    (p r : ℕ)
    (hkey :
      (Int.ofNat ((3 * (p ^ r)).choose (p ^ r))) ^ 2 -
          (Int.ofNat ((3 * (p ^ (r - 1))).choose (p ^ (r - 1)))) ^ 2 ≡
        (27 : ℤ) * (Int.ofNat ((2 * (p ^ r)).choose (p ^ r)) -
          Int.ofNat ((2 * (p ^ (r - 1))).choose (p ^ (r - 1))))
        [ZMOD ((p : ℤ) ^ (3 * r + 3))]) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD ((p : ℤ) ^ (3 * r + 3))] := by
  unfold a
  -- `hkey` says exactly that the difference of the two unfolded `a`-values is
  -- divisible by the target modulus; the remaining work is only integer algebra.
  rw [Int.modEq_iff_dvd] at hkey ⊢
  convert hkey using 1
  ring


/-- Lucas-specialized residue of `choose (2*p^s) (p^s)` modulo `p`. -/
lemma choose_two_prime_pow_mod_p_all (p s : ℕ) [Fact p.Prime] :
    ((Nat.choose (2 * p^s) (p^s) : ℕ) : ZMod p) = 2 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := 2 * p^(s+1)) (k := p^(s+1)) (p := p)
      have hz : (((2 * p^(s+1)).choose (p^(s+1)) : ℕ) : ZMod p) =
          ((((2 * p^(s+1)) % p).choose ((p^(s+1)) % p) *
            ((2 * p^(s+1)) / p).choose ((p^(s+1)) / p) : ℕ) : ZMod p) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact h
      rw [hz]
      have hp : p.Prime := Fact.out
      have hp0 : p ≠ 0 := hp.ne_zero
      have hpowmod : p^(s+1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (by omega))
      have h2powmod : (2 * p^(s+1)) % p = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 2)
      have hdiv1 : p^(s+1) / p = p^s := by
        rw [pow_succ']
        exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      have hdiv2 : (2 * p^(s+1)) / p = 2 * p^s := by
        rw [pow_succ']
        rw [show 2 * (p * p^s) = p * (2 * p^s) by ring]
        exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      rw [hpowmod, h2powmod, hdiv1, hdiv2]
      simp [ih]

/-- Lucas-specialized residue of `choose (3*p^s) (p^s)` modulo `p`.
The statement is intentionally `= 3`, which also means `= 0` in `ZMod 3`. -/
lemma choose_three_prime_pow_mod_p_all (p s : ℕ) [Fact p.Prime] :
    ((Nat.choose (3 * p^s) (p^s) : ℕ) : ZMod p) = 3 := by
  induction s with
  | zero => simp
  | succ s ih =>
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := 3 * p^(s+1)) (k := p^(s+1)) (p := p)
      have hz : (((3 * p^(s+1)).choose (p^(s+1)) : ℕ) : ZMod p) =
          ((((3 * p^(s+1)) % p).choose ((p^(s+1)) % p) *
            ((3 * p^(s+1)) / p).choose ((p^(s+1)) / p) : ℕ) : ZMod p) := by
        rw [ZMod.natCast_eq_natCast_iff]
        exact h
      rw [hz]
      have hp : p.Prime := Fact.out
      have hp0 : p ≠ 0 := hp.ne_zero
      have hpowmod : p^(s+1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (by omega))
      have h3powmod : (3 * p^(s+1)) % p = 0 :=
        Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 3)
      have hdiv1 : p^(s+1) / p = p^s := by
        rw [pow_succ']
        exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      have hdiv3 : (3 * p^(s+1)) / p = 3 * p^s := by
        rw [pow_succ']
        rw [show 3 * (p * p^s) = p * (3 * p^s) by ring]
        exact Nat.mul_div_right _ (Nat.pos_of_ne_zero hp0)
      rw [hpowmod, h3powmod, hdiv1, hdiv3]
      simp [ih]

/-- First-level necessary residue: all prime-power values have the same residue modulo `p`. -/
lemma a_prime_pow_mod_p_constant (p s : ℕ) [Fact p.Prime] :
    ((a (p^s) : ℤ) : ZMod p) = ((-45 : ℤ) : ZMod p) := by
  simp [a, choose_two_prime_pow_mod_p_all p s, choose_three_prime_pow_mod_p_all p s]
  ring

/-- The target congruence reduced all the way down to modulus `p`; this is a
checked weak version of the conjectured prime-power congruence. -/
lemma oeis_357569_prime_power_step_mod_p
    (p r : ℕ) (hp : Nat.Prime p) :
    a (p ^ r) ≡ a (p ^ (r - 1)) [ZMOD (p : ℤ)] := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [← ZMod.intCast_eq_intCast_iff]
  rw [a_prime_pow_mod_p_constant, a_prime_pow_mod_p_constant]

