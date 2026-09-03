import Submission.PrimeMultiplierRowRemainder
import Submission.LambertSharperOperatorBounds

/-!
An explicit size range for prime rows at even multiples of `p-1`.
These are auxiliary estimates; they do not settle Erdős 68.
-/

namespace PrimeMultiplierQuantitative

open PrimeMultiplierRowRemainder FactorialClearingIndex

/-- The uniform multinomial coefficient counts a subset of all words. Here
we prove the bound directly by grouping consecutive factorial factors. -/
lemma factorial_block_bound (j k : ℕ) :
    (j*k).factorial ≤ j^(j*k) * k.factorial^j := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      (j*(k+1)).factorial = (j*k).factorial * (j*k+1).ascFactorial j := by
        rw [Nat.factorial_mul_ascFactorial]
        congr 1
      _ ≤ (j^(j*k)*k.factorial^j) * (j*k+j)^j :=
        Nat.mul_le_mul ih (Nat.ascFactorial_le_pow_add (j*k) j)
      _ = j^(j*(k+1)) * (k+1).factorial^j := by
        rw [show j*k+j = j*(k+1) by ring, mul_pow,
          Nat.factorial_succ, mul_pow,
          show j*(k+1) = j*k+j by ring, pow_add]
        ring

lemma blockCoefficient_word_bound (j k : ℕ) :
    blockCoefficient j k ≤ j^(j*k) := by
  apply Nat.le_of_mul_le_mul_right (c := k.factorial^j) _ (by positivity)
  rw [blockCoefficient_identity]
  exact factorial_block_bound j k

/-- Exact removal of the extra prime power from the uniform multinomial. -/
lemma numerator_prime_power (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    numerator p j * p^(j-1) = blockCoefficient j (p-1) := by
  have hf : p.factorial = p*(p-1).factorial := by
    conv_lhs => rw [← Nat.sub_add_cancel hp.pos, Nat.factorial_succ]
    rw [Nat.sub_add_cancel hp.pos]
  have hpow : p^j = p*p^(j-1) := by
    conv_lhs => rw [← Nat.sub_add_cancel hj, pow_succ']
  have h := numerator_identity p j hp hj hjp
  rw [hf, mul_pow, hpow, ← blockCoefficient_identity j (p-1)] at h
  have h' : p * (numerator p j * p^(j-1) * (p-1).factorial^j) =
      p * (blockCoefficient j (p-1) * (p-1).factorial^j) := by
    nlinarith [h]
  have hc := Nat.eq_of_mul_eq_mul_left hp.pos h'
  exact Nat.eq_of_mul_eq_mul_right (by positivity : 0 < (p-1).factorial^j) hc

lemma numerator_word_bound (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    numerator p j ≤ j^(j*(p-1)) := by
  calc
    numerator p j ≤ numerator p j * p^(j-1) :=
      Nat.le_mul_of_pos_right _ (Nat.pow_pos hp.pos)
    _ = blockCoefficient j (p-1) := numerator_prime_power p j hp hj hjp
    _ ≤ _ := blockCoefficient_word_bound j (p-1)

lemma pow_le_factorial_of_three_mul_le (p a : ℕ) (hp : 0 < p) (ha : 3*a ≤ p) :
    a^p ≤ p.factorial := by
  have haR : (a : ℝ) ≤ (p : ℝ)/3 := by
    have h : 3*(a : ℝ) ≤ p := by exact_mod_cast ha
    linarith
  have hb := haR.trans (LambertSharperOperatorBounds.rate_lower_third p hp)
  have hc := pow_le_pow_left₀ (Nat.cast_nonneg a) hb p
  rw [LambertRawBounds.rate_pow p hp] at hc
  exact_mod_cast hc

lemma multiplier_lt_prime (p j : ℕ) (hj : 0 < j) (hsize : 6*j^j ≤ p) : j < p := by
  have h := Nat.le_self_pow hj.ne' j
  have hpos : 0 < j^j := by positivity
  omega

/-- Unlike an eventual bound for fixed `j`, this is uniform in both parameters. -/
theorem numerator_small_of_bound (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hsize : 6*j^j ≤ p) : numerator p j < p.factorial-1 := by
  have hjp := multiplier_lt_prime p j hj hsize
  have hC : numerator p j ≤ (j^j)^p := by
    calc
      _ ≤ j^(j*(p-1)) := numerator_word_bound p j hp hj hjp.le
      _ ≤ j^(j*p) := Nat.pow_le_pow_right hj (Nat.mul_le_mul_left j (Nat.sub_le p 1))
      _ = _ := pow_mul j j p
  have hf : (2*j^j)^p ≤ p.factorial :=
    pow_le_factorial_of_three_mul_le p (2*j^j) hp.pos (by omega)
  have hfour : 4 ≤ 2^p := by
    have h := Nat.pow_le_pow_right (by omega : 0 < 2) hp.two_le
    norm_num at h ⊢
    exact h
  rw [mul_pow] at hf
  have hm := Nat.mul_le_mul_right ((j^j)^p) hfour
  have hpos : 0 < (j^j)^p := by positivity
  omega

/-- The prime-row identity with a fully explicit size condition, allowing
`j` to vary with `p`. -/
theorem row_formula_of_bound (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (heven : Even j)
    (hsize : 6*j^j ≤ p) :
    RowRemainderBounds.rowRemainder (j*(p-1)) p = 1-1/(p : ℝ) +
      ((j*(p-1)).factorial : ℝ)/((p.factorial : ℝ)^j*(p.factorial-1)) :=
  row_formula p j hp hj heven (multiplier_lt_prime p j hj hsize)
    (numerator_small_of_bound p j hp hj hsize)

theorem tail_gt_of_bound (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (heven : Even j)
    (hsize : 6*j^j ≤ p) :
    1-1/(p : ℝ) < Erdos68Development.rowTail (j*(p-1)) :=
  tail_gt_one_sub_inv p j hp hj heven (multiplier_lt_prime p j hj hsize)
    (numerator_small_of_bound p j hp hj hsize)

#print axioms numerator_prime_power
#print axioms numerator_word_bound
#print axioms numerator_small_of_bound
#print axioms row_formula_of_bound
#print axioms tail_gt_of_bound

end PrimeMultiplierQuantitative
