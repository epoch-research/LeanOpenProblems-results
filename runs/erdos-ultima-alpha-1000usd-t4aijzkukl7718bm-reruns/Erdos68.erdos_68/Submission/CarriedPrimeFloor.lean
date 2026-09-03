import Submission.CarriedRationalPrimePattern

/-!
An explicit rational floor formula at prime successors for the actual
carried representation. This is a reformulation, not a settlement.
-/

namespace CarriedPrimeFloor

open Erdos68Development CongruencePreservingCarry

/-- The factorial-scaled carried prefix at original index `r+3`. -/
def scaledPrefix (r : ℕ) : ℤ := lambertPrefix (r+3)+CongruencePreservingCarry.carry r

lemma scaledPrefix_succ (r : ℕ) :
    scaledPrefix (r+1) = (r+4)*scaledPrefix r+coeffRow r := by
  simp only [scaledPrefix, coeffRow, show r+1+3 = (r+3)+1 by omega, lambertPrefix_succ]
  push_cast
  ring

lemma residual_eq (r : ℕ) : z r = scaledSumQ (r+2)-(scaledPrefix r : ℚ) := by
  simp [z, y, scaledPrefix]
  ring

lemma scaledPrefix_prime_successor_congruence (r : ℕ) (hp : (r+4).Prime) :
    (r+4 : ℤ) ∣ scaledPrefix (r+2)-2 := by
  have hd := coeffRow_congruence (r+1)
  have he : (r+1+3 : ℤ) = r+4 := by ring
  push_cast at hd
  rw [he] at hd
  rw [show r+2 = (r+1)+1 by omega, scaledPrefix_succ, scaledPrefix_succ,
    coeffRow_prime r hp]
  convert dvd_add (dvd_mul_right (r+4 : ℤ) ((r+5)*scaledPrefix r+1)) hd using 1
  push_cast
  ring

/-- At a prime successor the recursive carry is entirely determined by the
original rational partial sum at that index. -/
theorem scaledPrefix_prime_successor (r : ℕ) (hp : (r+4).Prime) :
    scaledPrefix (r+2) = 2+(r+4)*⌊(scaledSumQ (r+4)-2)/(r+4)⌋ := by
  have hnp : ¬(r+1+4).Prime := by
    simpa only [Nat.add_assoc] using
      CarriedRationalPrimePattern.prime_successor_not_prime (r+4) hp (by omega)
  have hz := z_nonprime_bounds (r+1) hnp
  rw [show r+1+1 = r+2 by omega, residual_eq] at hz
  norm_num only [Nat.add_assoc, Nat.reduceAdd, Nat.cast_add, Nat.cast_ofNat] at hz
  obtain ⟨k, hk⟩ := scaledPrefix_prime_successor_congruence r hp
  have he : scaledPrefix (r+2) = 2+(r+4 : ℤ)*k := by omega
  have heQ : (scaledPrefix (r+2) : ℚ) = 2+(r+4 : ℚ)*k := by exact_mod_cast he
  rw [heQ] at hz
  have hf : ⌊(scaledSumQ (r+4)-2)/(r+4)⌋ = k := by
    apply Int.floor_eq_iff.mpr
    constructor
    · apply (le_div_iff₀ (by positivity : (0 : ℚ) < r+4)).mpr
      nlinarith [hz.1]
    · apply (div_lt_iff₀ (by positivity : (0 : ℚ) < r+4)).mpr
      nlinarith [hz.2]
  rw [hf]
  exact he

def primeGridApprox (r : ℕ) : ℚ :=
  (r+4)*(⌊(scaledSumQ (r+4)-2)/(r+4)⌋+1 : ℤ)/(r+5).factorial

/-- The prime-successor grid omits the factor `p` from `(p+1)!`. -/
lemma primeGridApprox_grid (r : ℕ) :
    primeGridApprox r = (⌊(scaledSumQ (r+4)-2)/(r+4)⌋+1 : ℤ) /
      ((r+5)*(r+3).factorial : ℚ) := by
  have hp : (r+4 : ℚ) ≠ 0 := by positivity
  have hn : (r+5 : ℚ) ≠ 0 := by positivity
  have hf : ((r+3).factorial : ℚ) ≠ 0 := by positivity
  unfold primeGridApprox
  rw [show r+5 = (r+4)+1 by omega, Nat.factorial_succ,
    show r+4 = (r+3)+1 by omega, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma primeGridApprox_den_dvd (r : ℕ) :
    (primeGridApprox r).den ∣ (r+5)*(r+3).factorial := by
  have he : primeGridApprox r = Rat.divInt
      (⌊(scaledSumQ (r+4)-2)/(r+4)⌋+1)
      (((r+5)*(r+3).factorial : ℕ) : ℤ) := by
    rw [primeGridApprox_grid, Rat.divInt_eq_div]
    push_cast
    rfl
  rw [he]
  exact_mod_cast Rat.den_dvd
    (⌊(scaledSumQ (r+4)-2)/(r+4)⌋+1)
    (((r+5)*(r+3).factorial : ℕ) : ℤ)

lemma primeGridApprox_den_coprime (r : ℕ) (hp : (r+4).Prime) :
    (r+4).Coprime (primeGridApprox r).den := by
  have hc : (r+4).Coprime ((r+5)*(r+3).factorial) := by
    apply Nat.Coprime.mul_right
    · rw [show r+5 = (r+4)+1 by omega, Nat.coprime_self_add_right]
      exact Nat.coprime_one_right _
    · exact hp.coprime_factorial_of_lt (by omega)
  exact hc.of_dvd_right (primeGridApprox_den_dvd r)

lemma primeGridApprox_identity (r : ℕ) (hp : (r+4).Prime) :
    primeGridApprox r = ((scaledPrefix (r+2) : ℚ)+r+2)/(r+5).factorial := by
  rw [scaledPrefix_prime_successor r hp]
  unfold primeGridApprox
  push_cast
  congr 1
  ring

lemma tail_prime_successor (r : ℕ) (hp : (r+4).Prime) :
    tail (r+2) = (r+5).factorial*(∑' n : ℕ, term n)-
      2-(r+4)*((⌊(scaledSumQ (r+4)-2)/(r+4)⌋ : ℤ) : ℝ) := by
  change (r+2+3).factorial*(∑' n : ℕ, term n)-(scaledPrefix (r+2) : ℝ) = _
  rw [scaledPrefix_prime_successor r hp]
  push_cast
  ring

lemma primeGridApprox_error (r : ℕ) (hp : (r+4).Prime) :
    (r+5).factorial*((primeGridApprox r : ℝ)-(∑' n : ℕ, term n)) =
      r+2-tail (r+2) := by
  rw [primeGridApprox_identity r hp]
  have hf : ((r+5).factorial : ℝ) ≠ 0 := by positivity
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_natCast, Rat.cast_intCast,
    Rat.cast_ofNat, mul_sub, mul_div_cancel₀ _ hf, tail, scaledPrefix]
  push_cast
  ring

/-- A hypothetical rational value makes these explicit prime-grid
approximants eventually exactly constant. -/
theorem rational_primeGridApprox (q : ℚ) (hq : (∑' n : ℕ, term n) = (q : ℝ))
    (r : ℕ) (hp : (r+4).Prime) (hden : q.den ≤ r+3) : primeGridApprox r = q := by
  have hr : 5 ≤ r+4 := by
    by_contra hn
    have he : r = 0 := by omega
    subst r
    norm_num at hp
  have hpattern := CarriedRationalPrimePattern.rational_prime_successor q hq
    (r+4) hp hr (by omega)
  have hcast := CarriedRationalPrimePattern.integerTail_cast q hq (r+4+1) (by omega)
  have htail : tail (r+2) = r+2 := by
    rw [hpattern] at hcast
    have he := CarriedRationalPrimePattern.actualTail_add_three (r+2)
    rw [show r+2+3 = r+4+1 by omega] at he
    rw [he] at hcast
    push_cast at hcast
    linarith
  have he := primeGridApprox_error r hp
  rw [htail, sub_self, hq] at he
  have hz : (primeGridApprox r : ℝ)-(q : ℝ) = 0 :=
    (mul_eq_zero.mp he).resolve_left (by positivity)
  exact_mod_cast sub_eq_zero.mp hz

#print axioms scaledPrefix_prime_successor
#print axioms primeGridApprox_den_coprime
#print axioms primeGridApprox_error
#print axioms rational_primeGridApprox

end CarriedPrimeFloor
