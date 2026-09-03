import Submission.LambertBlockPowerCongruence

/-!
A common, exact modulus for all omitted Lambert columns in a finite window.
This is arithmetic for the original coefficients, not an irrationality proof.
-/

namespace CombinedColumnModulus

open Erdos68Development LambertBlockPowerCongruence

/-- A common denominator for column j at indices at most T. -/
def columnDenominator (T j : ℕ) : ℕ := (T/j).factorial^j

/-- Columns strictly beyond J. Columns with j>T have no contribution. -/
def highColumns (T J : ℕ) : Finset ℕ := (Finset.range (T+1)).filter (J < ·)

/-- This is an lcm, not a product of separately cleared denominators. -/
def highDenominator (T J : ℕ) : ℕ :=
  (highColumns T J).lcm (columnDenominator T)

def modulus (T J : ℕ) : ℕ := T.factorial / highDenominator T J

lemma columnDenominator_dvd_factorial (T j : ℕ) :
    columnDenominator T j ∣ T.factorial := by
  exact (factorial_pow_dvd_factorial_mul (T/j) j).trans
    (Nat.factorial_dvd_factorial (Nat.div_mul_le_self T j))

lemma highDenominator_dvd_factorial (T J : ℕ) :
    highDenominator T J ∣ T.factorial := by
  apply Finset.lcm_dvd
  intro j hj
  exact columnDenominator_dvd_factorial T j

lemma highDenominator_pos (T J : ℕ) : 0 < highDenominator T J :=
  Nat.pos_of_dvd_of_pos (highDenominator_dvd_factorial T J) (Nat.factorial_pos T)

lemma modulus_mul_denominator (T J : ℕ) :
    modulus T J * highDenominator T J = T.factorial :=
  Nat.div_mul_cancel (highDenominator_dvd_factorial T J)

lemma modulus_pos (T J : ℕ) : 0 < modulus T J :=
  Nat.div_pos (Nat.le_of_dvd (Nat.factorial_pos T) (highDenominator_dvd_factorial T J))
    (highDenominator_pos T J)

lemma high_summand_denominator_dvd (T J n d : ℕ) (hn : n ≤ T)
    (hd : d ∣ n) (hJ : J < n/d) :
    d.factorial^(n/d) ∣ highDenominator T J := by
  have hk0 : 0 < n/d := by omega
  have he : d*(n/d) = n := Nat.mul_div_cancel' hd
  have hdk : d ≤ T/(n/d) := (Nat.le_div_iff_mul_le hk0).mpr (by omega)
  have hmem : n/d ∈ highColumns T J := by
    simp only [highColumns, Finset.mem_filter, Finset.mem_range]
    exact ⟨(Nat.div_le_self n d).trans_lt (by omega), hJ⟩
  exact (pow_dvd_pow_of_dvd (Nat.factorial_dvd_factorial hdk) (n/d)).trans
    (Finset.dvd_lcm hmem)

lemma high_summand_quotient_dvd (T J n d : ℕ) (hn : n ≤ T)
    (hd : d ∣ n) (hJ : J < n/d) :
    modulus T J ∣ T.factorial / d.factorial^(n/d) :=
  Nat.div_dvd_div_left (highDenominator_dvd_factorial T J)
    (high_summand_denominator_dvd T J n d hn hd hJ)

lemma scaled_summand (T n d : ℕ) (hn : n ≤ T) (hd : d ∣ n) :
    (T.factorial/n.factorial) * (n.factorial/d.factorial^(n/d)) =
      T.factorial/d.factorial^(n/d) := by
  rw [← Nat.mul_div_assoc _ (lambertCoeff_divisible hd),
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial hn)]

/-- All columns beyond J disappear modulo this single exact modulus. -/
theorem scaled_coefficient_congruence (T J n : ℕ) (hn : n ≤ T) :
    Nat.ModEq (modulus T J)
      ((T.factorial/n.factorial)*lambertCoeff n)
      ((T.factorial/n.factorial)*lowBlockCoeff n J) := by
  unfold lambertCoeff lowBlockCoeff
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Nat.ModEq.sum
  intro d hd
  by_cases hd2 : 2 ≤ d
  · rw [if_pos hd2]
    by_cases hJ : n/d ≤ J
    · rw [if_pos ⟨hd2, hJ⟩]
    · rw [if_neg (by simp [hJ]), mul_zero,
        scaled_summand T n d hn (Nat.dvd_of_mem_divisors hd)]
      exact Nat.modEq_zero_iff_dvd.mpr
        (high_summand_quotient_dvd T J n d hn (Nat.dvd_of_mem_divisors hd) (by omega))
  · have hh : ¬(2 ≤ d ∧ n/d ≤ J) := fun h => hd2 h.1
    simp only [if_neg hd2, if_neg hh, mul_zero]
    rfl

/-- The combined modulus retains every factorial p-power for every prime
above the entire omitted-column row cutoff. -/
lemma highDenominator_coprime (T J p : ℕ) (hp : p.Prime) (hT : T < (J+1)*p) :
    p.Coprime (highDenominator T J) := by
  apply Nat.Coprime.of_dvd_right ((highColumns T J).lcm_dvd_prod (columnDenominator T))
  apply Nat.Coprime.prod_right
  intro j hj
  have hJ : J < j := (Finset.mem_filter.mp hj).2
  have hd : T/j < p := by
    by_contra h
    have hj0 : 0 < j := by omega
    have hh := Nat.mul_le_mul_right j (show p ≤ T/j by omega)
    have hdiv := Nat.div_mul_le_self T j
    nlinarith
  exact (hp.coprime_factorial_of_lt hd).pow_right j

lemma factorial_prime_power_dvd_modulus (T J p e : ℕ) (hp : p.Prime)
    (hT : T < (J+1)*p) (he : p^e ∣ T.factorial) : p^e ∣ modulus T J := by
  have hc := (highDenominator_coprime T J p hp hT).pow_left e
  apply hc.dvd_of_dvd_mul_left
  simpa only [Nat.mul_comm (highDenominator T J), modulus_mul_denominator] using he

/-- The statement also holds for signed weights, without a prime-by-prime
choice of normalizations. -/
theorem weighted_difference_divisible (T J : ℕ) (s : Finset ℕ) (w : ℕ → ℤ)
    (hs : ∀ n ∈ s, n ≤ T) :
    (modulus T J : ℤ) ∣ ∑ n ∈ s, w n * (T.factorial/n.factorial : ℕ) *
      ((lambertCoeff n : ℤ)-lowBlockCoeff n J) := by
  apply Finset.dvd_sum
  intro n hn
  have h := Nat.modEq_iff_dvd.mp (scaled_coefficient_congruence T J n (hs n hn)).symm
  have hm := dvd_mul_of_dvd_right h (w n)
  simp only [Nat.cast_mul] at hm
  convert hm using 1
  ring

/-- If the full scaled form is divisible, the retained low-column form is
also divisible. This is not a statement that either form is zero. -/
theorem low_form_divisible (T J : ℕ) (s : Finset ℕ) (w : ℕ → ℤ)
    (hs : ∀ n ∈ s, n ≤ T)
    (htotal : (modulus T J : ℤ) ∣
      ∑ n ∈ s, w n * (T.factorial/n.factorial : ℕ) * lambertCoeff n) :
    (modulus T J : ℤ) ∣
      ∑ n ∈ s, w n * (T.factorial/n.factorial : ℕ) * lowBlockCoeff n J := by
  have hd := weighted_difference_divisible T J s w hs
  simp only [mul_sub, Finset.sum_sub_distrib] at hd
  have h := dvd_sub htotal hd
  simpa only [sub_sub_cancel] using h

/-- Within divisors of T!, this is the largest modulus forced by clearing
all individual omitted-column denominators. -/
theorem maximal_modulus (T J m : ℕ) (hm : m ∣ T.factorial) :
    m ∣ modulus T J ↔
      ∀ j ∈ highColumns T J, m ∣ T.factorial / columnDenominator T j := by
  constructor
  · intro h j hj
    exact h.trans (Nat.div_dvd_div_left (highDenominator_dvd_factorial T J)
      (Finset.dvd_lcm hj))
  · intro h
    have hD : highDenominator T J ∣ T.factorial/m := by
      apply Finset.lcm_dvd
      intro j hj
      apply (Nat.dvd_div_iff_mul_dvd hm).mpr
      have hh := (Nat.dvd_div_iff_mul_dvd (columnDenominator_dvd_factorial T j)).mp
        (h j hj)
      simpa only [Nat.mul_comm] using hh
    apply (Nat.dvd_div_iff_mul_dvd (highDenominator_dvd_factorial T J)).mpr
    have hh := (Nat.dvd_div_iff_mul_dvd hm).mp hD
    simpa only [Nat.mul_comm] using hh

/-- The first omitted column already bounds the entire combined modulus;
its denominator cannot be ignored when estimating the gain. -/
lemma modulus_le_first_column_quotient (T J : ℕ) (hJ : J < T) :
    modulus T J ≤ T.factorial / (T/(J+1)).factorial^(J+1) := by
  have hj : J+1 ∈ highColumns T J := by
    simp only [highColumns, Finset.mem_filter, Finset.mem_range]
    omega
  have hd := Nat.div_dvd_div_left (highDenominator_dvd_factorial T J)
    (Finset.dvd_lcm hj)
  apply Nat.le_of_dvd ?_ hd
  exact Nat.div_pos
    (Nat.le_of_dvd (Nat.factorial_pos T) (columnDenominator_dvd_factorial T (J+1)))
    (by unfold columnDenominator; positivity)

/-- A small exact instance includes factors from primes below the cutoff:
M(12,2)=2*3*5^2*7*11, rather than just 5^2*7*11. -/
lemma exact_modulus_example : highDenominator 12 2 = 41472 ∧ modulus 12 2 = 11550 := by
  decide

end CombinedColumnModulus

#print axioms CombinedColumnModulus.scaled_coefficient_congruence
#print axioms CombinedColumnModulus.factorial_prime_power_dvd_modulus
#print axioms CombinedColumnModulus.weighted_difference_divisible
#print axioms CombinedColumnModulus.low_form_divisible
#print axioms CombinedColumnModulus.exact_modulus_example

#print axioms CombinedColumnModulus.maximal_modulus
#print axioms CombinedColumnModulus.modulus_le_first_column_quotient
