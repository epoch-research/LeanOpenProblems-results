import Submission.LambertPrimeScaling

/-!
Removing a prime-power factor from the index of the original Lambert
coefficients, modulo that prime. These are auxiliary coefficient facts,
not a proof of Erdős 68 and not congruences for a carried representation.
-/

namespace LambertPrimePowerScaling

open Erdos68Development LambertPrimeScaling

lemma fullCoeff_prime_pow_scaling (p r m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Nat.ModEq p (fullCoeff (p^r*m)) (fullCoeff m) := by
  have hp0 := hp.pos
  induction r with
  | zero => simp only [pow_zero, one_mul]; rfl
  | succ r ih =>
    rw [pow_succ', mul_assoc]
    exact (fullCoeff_prime_scaling p (p^r*m) hp (by positivity)).trans ih

/-- A positive power of the prime can be removed in one step. The singleton
block correction on the right is essential when `m < p`. -/
theorem lambertCoeff_prime_pow_scaling (p r m : ℕ) (hp : p.Prime) (hm : 0 < m) :
    Nat.ModEq p (lambertCoeff (p^(r+1)*m)) (lambertCoeff m+m.factorial) := by
  have hp0 := hp.pos
  have hn : 0 < p^(r+1)*m := by positivity
  have h := fullCoeff_prime_pow_scaling p (r+1) m hp hm
  rw [fullCoeff_eq _ hn, fullCoeff_eq m hm] at h
  have hpn : p ≤ p^(r+1)*m := by
    rw [pow_succ', mul_assoc]
    exact Nat.le_mul_of_pos_right p (by positivity)
  have hd : p ∣ (p^(r+1)*m).factorial := Nat.dvd_factorial hp.pos hpn
  have he : Nat.ModEq p
      (lambertCoeff (p^(r+1)*m)+(p^(r+1)*m).factorial)
      (lambertCoeff (p^(r+1)*m)) := by
    simpa only [Nat.add_zero] using
      (Nat.ModEq.refl (lambertCoeff (p^(r+1)*m))).add
        (Nat.modEq_zero_iff_dvd.mpr hd)
  exact he.symm.trans h

/-- Every prime-power-indexed original coefficient is one modulo the prime. -/
theorem lambertCoeff_prime_power_modEq_one (p r : ℕ) (hp : p.Prime) :
    Nat.ModEq p (lambertCoeff (p^(r+1))) 1 := by
  have h := lambertCoeff_prime_pow_scaling p r 1 hp (by decide)
  have h1 : lambertCoeff 1 = 0 := by simp [lambertCoeff]
  simpa only [mul_one, h1, Nat.factorial_one, Nat.zero_add] using h

theorem prime_dvd_prime_power_coeff_sub_one (p r : ℕ) (hp : p.Prime) :
    p ∣ lambertCoeff (p^(r+1))-1 := by
  have h := lambertCoeff_prime_power_modEq_one p r hp
  have ha : 1 ≤ lambertCoeff (p^(r+1)) := by
    have he : lambertCoeff (p^(r+1)) % p = 1 := by
      simpa only [Nat.ModEq, Nat.mod_eq_of_lt hp.one_lt] using h
    have := Nat.mod_le (lambertCoeff (p^(r+1))) p
    omega
  exact (Nat.modEq_iff_dvd' ha).mp h.symm

#print axioms lambertCoeff_prime_pow_scaling
#print axioms lambertCoeff_prime_power_modEq_one
#print axioms prime_dvd_prime_power_coeff_sub_one

end LambertPrimePowerScaling
