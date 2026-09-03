import Submission.CompositeDivisorReflection

/-! An elementary coverage criterion for two-factor divisor marks. -/
namespace Erdos371
open Finset

/-- A divisor just above k is no larger than k times the largest prime factor.
The proof chooses the least qualifying divisor and removes one prime factor. -/
lemma exists_divisor_above_le_mul_maxPrimeFac (m k : ℕ)
    (hk : 1 ≤ k) (hkm : k < m) :
    ∃ d : ℕ, d ∣ m ∧ k < d ∧ d ≤ k * Nat.maxPrimeFac m := by
  have hex : ∃ d : ℕ, d ∣ m ∧ k < d := ⟨m,dvd_refl m,hkm⟩
  let d := Nat.find hex
  have hd : d ∣ m ∧ k < d := Nat.find_spec hex
  have hd1 : 1 < d := by omega
  let r := d.minFac
  have hr : r.Prime := Nat.minFac_prime (by omega)
  have hrd : r ∣ d := Nat.minFac_dvd d
  have hrm : r ∣ m := hrd.trans hd.1
  have hrl : r ≤ Nat.maxPrimeFac m := Nat.le_maxPrimeFac (by omega) hr hrm
  have hqd : d/r < d := Nat.div_lt_self (by omega) hr.one_lt
  have hqk : d/r ≤ k := by
    by_contra h
    have hq : d/r ∣ m := (Nat.div_dvd_of_dvd hrd).trans hd.1
    exact Nat.find_min hex hqd ⟨hq,by omega⟩
  refine ⟨d,hd.1,hd.2,?_⟩
  calc
    d = (d/r)*r := (Nat.div_mul_cancel hrd).symm
    _ ≤ k * Nat.maxPrimeFac m := Nat.mul_le_mul hqk hrl

/-- An integer with all prime factors below p, and size below p^(3/2),
splits into two factors below p.
The squared inequality avoids real powers and any rounding convention. -/
theorem exists_two_factors_lt_of_square_lt_cube (m p : ℕ) (hm : 1 < m)
    (hmp : Nat.maxPrimeFac m < p) (hsize : m^2 < p^3) :
    ∃ a b : ℕ, 2 ≤ a ∧ a < p ∧ 1 ≤ b ∧ b < p ∧ a*b = m := by
  have hq : (Nat.maxPrimeFac m).Prime := Nat.prime_maxPrimeFac_of_one_lt m hm
  have hp : 2 < p := hq.two_le.trans_lt hmp
  by_cases hsmall : m < p
  · exact ⟨m,1,by omega,hsmall,le_rfl,by omega,by simp⟩
  have hk : 1 ≤ m/p := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hklt : m/p < m := Nat.div_lt_self (by omega) (by omega)
  have hksq : (m/p)^2 < p := by
    have hmul : (m/p)*p ≤ m := Nat.div_mul_le_self m p
    have hs : ((m/p)*p)^2 ≤ m^2 := Nat.pow_le_pow_left hmul 2
    by_contra h
    have hge : p ≤ (m/p)^2 := by omega
    have hprod := Nat.mul_le_mul_right (p^2) hge
    rw [mul_pow] at hs
    have he : p*p^2 = p^3 := by ring
    rw [he] at hprod
    omega
  by_cases hlarge : m/p < Nat.maxPrimeFac m
  · refine ⟨Nat.maxPrimeFac m,m/Nat.maxPrimeFac m,hq.two_le,hmp,?_,?_,?_⟩
    · apply (Nat.le_div_iff_mul_le hq.pos).mpr
      simpa using (Nat.maxPrimeFac_le (n := m))
    · apply (Nat.div_lt_iff_lt_mul hq.pos).mpr
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mp hlarge |>.trans_eq (Nat.mul_comm _ _)
    · exact Nat.mul_div_cancel' Nat.maxPrimeFac_dvd
  · obtain ⟨a,had,hka,habound⟩ := exists_divisor_above_le_mul_maxPrimeFac m (m/p) hk hklt
    have hap : a < p := by
      apply (habound.trans (Nat.mul_le_mul_left (m/p) (not_lt.mp hlarge))).trans_lt
      simpa only [pow_two] using hksq
    have ha0 : 0 < a := by omega
    refine ⟨a,m/a,by omega,hap,?_,?_,Nat.mul_div_cancel' had⟩
    · apply (Nat.le_div_iff_mul_le ha0).mpr
      simpa using Nat.le_of_dvd (by omega : 0 < m) had
    · apply (Nat.div_lt_iff_lt_mul ha0).mpr
      exact (Nat.div_lt_iff_lt_mul (by omega : 0 < p)).mp hka |>.trans_eq (Nat.mul_comm _ _)

#print axioms exists_divisor_above_le_mul_maxPrimeFac
#print axioms exists_two_factors_lt_of_square_lt_cube
end Erdos371
