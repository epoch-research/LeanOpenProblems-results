import Submission.PrimeMultiplierQuantitative

/-!
Parity and an exponentially small correction in the prime-row formulas.
These identities concern individual rational rows, not the irrationality
of the full sum.
-/

namespace PrimeMultiplierParity

open PrimeMultiplierRowRemainder PrimeMultiplierQuantitative
  FactorialClearingIndex RowRemainderBounds

noncomputable def correction (p j : ℕ) : ℝ :=
  ((j*(p-1)).factorial : ℝ)/((p.factorial : ℝ)^j*(p.factorial-1))

lemma factorial_sub_pos (p : ℕ) (hp : p.Prime) : (0 : ℝ) < p.factorial-1 := by
  have h : (2 : ℝ) ≤ p.factorial := by
    exact_mod_cast (show 2 ≤ p.factorial by simpa using Nat.factorial_le hp.two_le)
  linarith

lemma correction_pos (p j : ℕ) (hp : p.Prime) : 0 < correction p j := by
  have h := factorial_sub_pos p hp
  unfold correction
  positivity

lemma factorial_ratio (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    ((j*(p-1)).factorial : ℝ)/(p.factorial : ℝ)^j = (numerator p j : ℝ)/p := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have he : (numerator p j : ℝ)*(p.factorial : ℝ)^j =
      (p : ℝ)*(j*(p-1)).factorial := by
    exact_mod_cast numerator_identity p j hp hj hjp
  apply (div_eq_div_iff (by positivity) hpR.ne').mpr
  nlinarith

lemma correction_eq (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    correction p j = (numerator p j : ℝ)/((p : ℝ)*(p.factorial-1)) := by
  unfold correction
  rw [← div_div, factorial_ratio p j hp hj hjp, div_div]

lemma numerator_pos (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hjp : j ≤ p) :
    0 < numerator p j := by
  have h := blockCoefficient_pos j (p-1)
  rw [← numerator_prime_power p j hp hj hjp] at h
  exact Nat.pos_of_mul_pos_right h

lemma factorial_dominates_numerator (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hsize : 6*j^j ≤ p) : 2^p * numerator p j ≤ p.factorial := by
  have hjp := multiplier_lt_prime p j hj hsize
  have hC : numerator p j ≤ (j^j)^p := by
    calc
      _ ≤ j^(j*(p-1)) := numerator_word_bound p j hp hj hjp.le
      _ ≤ j^(j*p) := Nat.pow_le_pow_right hj (Nat.mul_le_mul_left j (Nat.sub_le p 1))
      _ = _ := pow_mul j j p
  have hf := pow_le_factorial_of_three_mul_le p (2*j^j) hp.pos (by omega)
  calc
    2^p * numerator p j ≤ 2^p * (j^j)^p := Nat.mul_le_mul_left _ hC
    _ = (2*j^j)^p := (mul_pow _ _ _).symm
    _ ≤ _ := hf

lemma two_pow_ge_four (p : ℕ) (hp : p.Prime) : (4 : ℝ) ≤ 2^p := by
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp.two_le
  norm_num at h
  exact h

/-- The correction is not merely smaller than `1/p`: in the explicit
uniform range it has an exponentially small bound. -/
theorem correction_le (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hsize : 6*j^j ≤ p) :
    correction p j ≤ 1/((p : ℝ)*(2^p-1)) := by
  have hjp := multiplier_lt_prime p j hj hsize
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hdR := factorial_sub_pos p hp
  have htwo := two_pow_ge_four p hp
  have htwo' : (0 : ℝ) < 2^p-1 := by linarith
  have hC : (1 : ℝ) ≤ numerator p j := by
    exact_mod_cast numerator_pos p j hp hj hjp.le
  have hf : (2 : ℝ)^p * numerator p j ≤ p.factorial := by
    exact_mod_cast factorial_dominates_numerator p j hp hj hsize
  have hmain : (numerator p j : ℝ)*(2^p-1) ≤ p.factorial-1 := by nlinarith
  rw [correction_eq p j hp hj hjp.le]
  apply (div_le_div_iff₀ (mul_pos hpR hdR) (mul_pos hpR htwo')).mpr
  nlinarith [mul_le_mul_of_nonneg_left hmain hpR.le]

lemma correction_lt_inv (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hsize : 6*j^j ≤ p) : correction p j < 1/(p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  apply (correction_le p j hp hj hsize).trans_lt
  apply one_div_lt_one_div_of_lt hpR
  have h := two_pow_ge_four p hp
  nlinarith

/-- A version that leaves the numerator's residue unevaluated. -/
lemma row_formula_mod (p j : ℕ) (hp : p.Prime) (hj : 0 < j)
    (hsize : 6*j^j ≤ p) :
    rowRemainder (j*(p-1)) p = ((numerator p j % p : ℕ) : ℝ)/p + correction p j := by
  have hjp := multiplier_lt_prime p j hj hsize
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hn : (j-1)*p ≤ j*(p-1) := by
    have h₁ := Nat.sub_add_cancel hj
    have h₂ := Nat.sub_add_cancel hp.pos
    nlinarith
  obtain ⟨I, hI⟩ := geometric_decomposition (j*(p-1)) p j hp.two_le hj hn
  have hdiv : (numerator p j : ℝ)/p = (numerator p j / p : ℕ) +
      ((numerator p j % p : ℕ) : ℝ)/p := by
    have h : ((numerator p j % p : ℕ) : ℝ) + (p : ℝ)*(numerator p j / p : ℕ) =
        numerator p j := by exact_mod_cast Nat.mod_add_div (numerator p j) p
    apply (div_eq_iff hpR.ne').mpr
    field_simp
    nlinarith
  have htotal : ((j*(p-1)).factorial : ℝ)/(p.factorial-1) =
      ((I + numerator p j / p : ℕ) : ℝ) +
        (((numerator p j % p : ℕ) : ℝ)/p + correction p j) := by
    rw [hI, factorial_ratio p j hp hj hjp.le, hdiv, Nat.cast_add]
    unfold correction
    ring
  have hnonneg : 0 ≤ ((numerator p j % p : ℕ) : ℝ)/p + correction p j :=
    add_nonneg (by positivity) (correction_pos p j hp).le
  have hres : ((numerator p j % p : ℕ) : ℝ)+1 ≤ p := by
    exact_mod_cast (show numerator p j % p + 1 ≤ p by
      have h := Nat.mod_lt (numerator p j) hp.pos
      omega)
  have hupper : ((numerator p j % p : ℕ) : ℝ)/p + correction p j < 1 := by
    have hc := correction_lt_inv p j hp hj hsize
    have hm : ((numerator p j % p : ℕ) : ℝ)/p + 1/(p : ℝ) ≤ 1 := by
      rw [← add_div]
      exact (div_le_one hpR).mpr hres
    linarith
  unfold rowRemainder
  rw [htotal, Int.fract_natCast_add, Int.fract_eq_self.mpr ⟨hnonneg, hupper⟩]

/-- The odd-multiplier counterpart to the earlier even-multiplier formula. -/
theorem odd_row_formula (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (hodd : Odd j)
    (hsize : 6*j^j ≤ p) :
    rowRemainder (j*(p-1)) p = 1/(p : ℝ) + correction p j := by
  have hjp := multiplier_lt_prime p j hj hsize
  have heven : Even (j-1) := by
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hcast : (numerator p j : ZMod p) = 1 := by
    rw [numerator_cast p j hp hj hjp, heven.neg_one_pow]
  have hmod : numerator p j % p = 1 := by
    have hc : (numerator p j : ZMod p) = ((1 : ℕ) : ZMod p) := by simpa using hcast
    have h := (ZMod.natCast_eq_natCast_iff (numerator p j) 1 p).mp hc
    change numerator p j % p = 1 % p at h
    simpa [Nat.mod_eq_of_lt hp.one_lt] using h
  rw [row_formula_mod p j hp hj hsize, hmod, Nat.cast_one]

/-- At a pair of consecutive even/odd multipliers, the two fractional
parts sum to just above one. This still concerns a single prime row. -/
theorem paired_row_bounds (p j : ℕ) (hp : p.Prime) (hj : 0 < j) (heven : Even j)
    (hsize : 6*j^j ≤ p) (hsize' : 6*(j+1)^(j+1) ≤ p) :
    1 < rowRemainder (j*(p-1)) p + rowRemainder ((j+1)*(p-1)) p ∧
    rowRemainder (j*(p-1)) p + rowRemainder ((j+1)*(p-1)) p ≤
      1 + 2/((p : ℝ)*(2^p-1)) := by
  have hodd : Odd (j+1) := by
    obtain ⟨k, hk⟩ := heven
    exact ⟨k, by omega⟩
  have he := row_formula_of_bound p j hp hj heven hsize
  change rowRemainder (j*(p-1)) p = 1-1/(p : ℝ)+correction p j at he
  rw [he, odd_row_formula p (j+1) hp (by omega) hodd hsize']
  have hp₁ := correction_pos p j hp
  have hp₂ := correction_pos p (j+1) hp
  have hb₁ := correction_le p j hp hj hsize
  have hb₂ := correction_le p (j+1) hp (by omega) hsize'
  have hd : 2/((p : ℝ)*(2^p-1)) =
      1/((p : ℝ)*(2^p-1)) + 1/((p : ℝ)*(2^p-1)) := by ring
  rw [hd]
  constructor <;> linarith

#print axioms factorial_dominates_numerator
#print axioms correction_le
#print axioms row_formula_mod
#print axioms odd_row_formula
#print axioms paired_row_bounds

end PrimeMultiplierParity
