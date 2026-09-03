import FormalConjecturesUtil
import Submission.CofactorDiscrepancy

/-! The first nontrivial winning-prime fiber, expressed exactly using two
prime indicators. This is a local identity, not an asymptotic cancellation
estimate and not a proof or disproof of Erdős 371. -/

namespace Erdos371TwoCofactorPrimeGroup

open Finset Erdos371PrimeDiscrepancy Erdos371CofactorDiscrepancy

/-- Below three times the cutoff, an odd integer above the cutoff has a
prime factor above the cutoff exactly when the integer itself is prime. -/
lemma odd_primefac_below_iff {m p : ℕ} (hp : 2 ≤ p) (hlo : p < m)
    (hhi : m < 3*p) (ho : Odd m) : P m < p ↔ ¬m.Prime := by
  constructor
  · intro h hm
    change m.maxPrimeFac < p at h
    rw [hm.maxPrimeFac_eq_self] at h
    omega
  · intro hm
    by_contra h
    have hq : (P m).Prime := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
    obtain ⟨b, hb⟩ := (Nat.maxPrimeFac_dvd : P m ∣ m)
    have hb0 : 0 < b := by nlinarith
    have hb3 : b < 3 := by nlinarith
    have hb1 : b ≠ 1 := by
      intro he
      simp only [he, mul_one] at hb
      exact hm (hb ▸ hq)
    have hb2 : b = 2 := by omega
    have hd : 2 ∣ m := by rw [hb, hb2]; exact dvd_mul_left 2 (P m)
    exact ho.not_two_dvd_nat hd

lemma twice_minus_odd (p : ℕ) (hp : 0 < p) : Odd (2*p-1) := by
  apply Nat.odd_iff.mpr
  omega

lemma twice_plus_odd (p : ℕ) : Odd (2*p+1) := by
  apply Nat.odd_iff.mpr
  omega

/-- At the endpoint immediately after the second multiple, the two local
prime obstructions are the entire signed winning-prime group. -/
theorem group_twice_add_one {p : ℕ} (hp : p.Prime) (hp2 : 2 < p) :
    group p (2*p+1) =
      (if (2*p+1).Prime then (1 : ℤ) else 0) -
      (if (2*p-1).Prime then (1 : ℤ) else 0) := by
  have hdiv : (2*p+1)/p = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hI : Icc 1 2 = ({1,2} : Finset ℕ) := by decide +kernel
  have hpm : P (p-1) < p := Nat.maxPrimeFac_le.trans_lt (by omega)
  have hpp : P (p+1) < p := after_odd_prime hp hp2
  have htwo : P 2 ≤ p := by norm_num [P]; omega
  have hone : P 1 ≤ p := by norm_num [P]; omega
  have hmul : P (2*p) = p := (prime_multiple_iff hp (by omega)).mpr htwo
  have hne : P (2*p+1) ≠ p := by
    simpa only [hmul] using consecutive_ne (2*p)
  have hm : P (2*p-1) < p ↔ ¬(2*p-1).Prime :=
    odd_primefac_below_iff hp.two_le (by omega) (by omega) (twice_minus_odd p hp.pos)
  have hh : P (2*p+1) < p ↔ ¬(2*p+1).Prime :=
    odd_primefac_below_iff hp.two_le (by omega) (by omega) (twice_plus_odd p)
  rw [group_eq_cofactorDifference hp]
  simp only [hne, false_and, if_false, add_zero, cofactorDifference, hdiv, hI]
  simp only [filter_insert, filter_singleton, one_mul, hone, htwo, hpm, hpp,
    true_and, and_self, if_true, hm, hh]
  by_cases hminus : (2*p-1).Prime <;> by_cases hplus : (2*p+1).Prime <;>
    simp [hminus, hplus]

end Erdos371TwoCofactorPrimeGroup

#print axioms Erdos371TwoCofactorPrimeGroup.group_twice_add_one
