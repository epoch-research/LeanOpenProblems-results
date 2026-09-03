import Submission.CarriedRationalPrimePattern
import Submission.LambertPrimeScaling

/-!
A conditional arithmetic criterion using coefficients at twice a prime.
No inheritance theorem for the required carried-coefficient congruence is
asserted, and the original conjecture is not settled.
-/

namespace CarriedTwicePrimeCriterion

open Erdos68Development CongruencePreservingCarry CarriedRationalPrimePattern

lemma twice_not_prime (p : ℕ) (hp : 2 ≤ p) : ¬(2*p).Prime := by
  intro h
  have hd := h.eq_two_or_odd
  omega

lemma last_prime_before_twice (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hcomp : ¬(2*p-1).Prime) :
    ∃ r : ℕ, r.Prime ∧ p < r ∧ r+1 < 2*p ∧
      ∀ n : ℕ, r < n → n ≤ 2*p → ¬n.Prime := by
  obtain ⟨s, hs, hps, hs2⟩ := Nat.exists_prime_lt_and_le_two_mul p hp.ne_zero
  have hslt : s < 2*p := by
    have hn := twice_not_prime p (by omega)
    by_contra h
    have he : s = 2*p := by omega
    exact hn (he ▸ hs)
  let S := (Finset.range (2*p)).filter Nat.Prime
  have hmem : s ∈ S := by simp only [S, Finset.mem_filter, Finset.mem_range]; exact ⟨hslt, hs⟩
  let r := S.max' ⟨s, hmem⟩
  have hrmem : r ∈ S := Finset.max'_mem _ _
  have hpr : p < r := hps.trans_le (Finset.le_max' S s hmem)
  have hrp : r.Prime := (Finset.mem_filter.mp hrmem).2
  have hrlt : r < 2*p := Finset.mem_range.mp (Finset.mem_filter.mp hrmem).1
  have hrne : r ≠ 2*p-1 := by intro he; exact hcomp (he ▸ hrp)
  refine ⟨r, hrp, hpr, by omega, ?_⟩
  intro n hrn hn hnp
  by_cases he : n = 2*p
  · exact twice_not_prime p (by omega) (he ▸ hnp)
  · have hnm : n ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hnp⟩
    have hh : n ≤ r := Finset.le_max' S n hnm
    omega

lemma rational_coeff_composite_run (q : ℚ) (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (p r : ℕ) (hp5 : 5 ≤ p) (hden : q.den ≤ p)
    (hr : r.Prime) (hpr : p < r) (hr2p : r+1 < 2*p)
    (hgap : ∀ n : ℕ, r < n → n ≤ 2*p → ¬n.Prime) :
    coeff (2*p) = 1+(2*(p : ℤ)-1)*(2*(r : ℤ)-2*p) := by
  have hstart := rational_prime_successor q hq r hr (by omega) (by omega)
  have hb := descending_block (integerTail q) r (2*p-r-1) (by omega) (by omega)
    hstart
    (fun i hi => integerTail_nonprime_bounds q hq (r+1+i) (by omega) (by omega)
      (hgap _ (by omega) (by omega)))
    (fun i hi => integerTail_congruence q hq (r+1+i) (by omega) (by omega))
  have hprev : integerTail q (2*p-1) = 2*(r : ℤ)-2*p := by
    have h := hb (2*p-r-2) (by omega)
    rw [show r+1+(2*p-r-2) = 2*p-1 by omega] at h
    omega
  have hnext : integerTail q (2*p) = 2*(r : ℤ)-1-2*p := by
    have h := hb (2*p-r-1) le_rfl
    rw [show r+1+(2*p-r-1) = 2*p by omega] at h
    omega
  have he := integerTail_succ q hq (2*p-1) (by omega)
  rw [show 2*p-1+1 = 2*p by omega, hprev, hnext] at he
  rw [Nat.cast_sub (show 1 ≤ 2*p by omega)] at he
  push_cast at he
  nlinarith

/-- Rationality forces a failure of the original twice-prime congruence in
the carried coefficients at every sufficiently late p with 2p-1 composite. -/
theorem rational_twice_prime_not_congruent (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ))
    (p : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hden : q.den ≤ p)
    (hcomp : ¬(2*p-1).Prime) : ¬(p : ℤ) ∣ coeff (2*p)-3 := by
  obtain ⟨r, hr, hpr, hr2p, hgap⟩ := last_prime_before_twice p hp hp5 hcomp
  have he := rational_coeff_composite_run q hq p r hp5 hden hr hpr hr2p hgap
  intro hd
  have htwo : (p : ℤ) ∣ 2*(r+1 : ℤ) := by
    convert dvd_sub (dvd_mul_right (p : ℤ) (4*r-4*p+2)) hd using 1
    rw [he]
    ring
  have htwoN : p ∣ 2*(r+1) := by exact_mod_cast htwo
  have hnp2 : ¬p ∣ 2 := by intro h; have := Nat.le_of_dvd (by omega : 0 < 2) h; omega
  have hpr1 : p ∣ r+1 := (hp.dvd_mul.mp htwoN).resolve_left hnp2
  have hdif : p ∣ r+1-p := Nat.dvd_sub hpr1 (dvd_refl p)
  have hz := Nat.eq_zero_of_dvd_of_lt hdif (show r+1-p < p by omega)
  omega

/-- The twice-prime congruence survives carrying exactly when the carry
at that index is divisible by the prime. This does not assert divisibility. -/
lemma twice_prime_congruence_iff_carry_dvd (p : ℕ) (hp : p.Prime) :
    (p : ℤ) ∣ coeff (2*p)-3 ↔
      (p : ℤ) ∣ CongruencePreservingCarry.carry (2*p-3) := by
  have hp2 := hp.two_le
  have ha : (p : ℤ) ∣ (lambertCoeff (2*p) : ℤ)-3 := by
    have he := Int.natCast_modEq_iff.mpr (LambertPrimeScaling.lambertCoeff_twice_prime p hp)
    simpa using Int.modEq_iff_dvd.mp he.symm
  have hm : (p : ℤ) ∣ (2*(p : ℤ))*CongruencePreservingCarry.carry (2*p-4) := by
    exact ⟨2*CongruencePreservingCarry.carry (2*p-4), by ring⟩
  have he : coeff (2*p) = (lambertCoeff (2*p) : ℤ) +
      CongruencePreservingCarry.carry (2*p-3) -
      (2*(p : ℤ))*CongruencePreservingCarry.carry (2*p-4) := by
    rw [coeff, if_neg (show ¬2*p < 4 by omega), coeffRow]
    rw [show 2*p-4+4 = 2*p by omega, show 2*p-4+1 = 2*p-3 by omega]
    have hn : ((2*p-4 : ℕ) : ℤ)+4 = 2*(p : ℤ) := by omega
    rw [hn]
  rw [he, show (lambertCoeff (2*p) : ℤ) +
      CongruencePreservingCarry.carry (2*p-3) -
      (2*(p : ℤ))*CongruencePreservingCarry.carry (2*p-4) - 3 =
      ((lambertCoeff (2*p) : ℤ)-3 + CongruencePreservingCarry.carry (2*p-3)) -
      (2*(p : ℤ))*CongruencePreservingCarry.carry (2*p-4) by ring]
  exact (dvd_sub_left hm).trans (dvd_add_right ha)

lemma prime_mod_three_predecessor_composite (p : ℕ) (hp5 : 5 ≤ p)
    (hmod : p % 3 = 2) : ¬(2*p-1).Prime := by
  have hdiv : 3 ∣ 2*p-1 := by omega
  intro hp
  have he : 2*p-1 = 3 := (hp.eq_one_or_self_of_dvd 3 hdiv).resolve_left (by omega) |>.symm
  omega

/-- Only arbitrarily large successful inheritance indices are needed; the
congruence need not hold at every sufficiently late prime. -/
theorem irrational_of_frequent_twice_prime_congruence
    (hc : ∀ M : ℕ, ∃ p ≥ M, p.Prime ∧ ¬(2*p-1).Prime ∧
      (p : ℤ) ∣ coeff (2*p)-3) : Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hlarge, hp, hcomp, hdiv⟩ := hc (max q.den 5)
  exact rational_twice_prime_not_congruent q hq.symm p hp (by omega) (by omega) hcomp hdiv

/-- It would suffice to retain a_{2p}=3 modulo p eventually at primes
p=2 modulo 3. No such inheritance is proved for the carried coefficients. -/
theorem irrational_of_twice_prime_congruences (N : ℕ)
    (hc : ∀ p ≥ N, p.Prime → p % 3 = 2 → (p : ℤ) ∣ coeff (2*p)-3) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨p, hlarge, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max (max N q.den) 5) (q := 3) (a := 2) (by omega) (by decide)
  have hmod' : p % 3 = 2 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  apply rational_twice_prime_not_congruent q hq.symm p hp (by omega) (by omega)
    (prime_mod_three_predecessor_composite p (by omega) hmod')
  exact hc p (by omega) hp hmod'

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- A finite warning: the new original-coefficient congruence is not an
automatic property of the carried coefficients. -/
lemma finite_inheritance_failure : coeff 10 = 55 ∧ ¬(5 : ℤ) ∣ coeff 10-3 := by
  have h3 : lambertPrefix 3 = 4 := by decide
  have h4 : lambertPrefix 4 = 23 := by decide
  have h5 : lambertPrefix 5 = 116 := by decide
  have h6 : lambertPrefix 6 = 807 := by decide
  have h7 : lambertPrefix 7 = 5650 := by decide
  have h8 : lambertPrefix 8 = 47791 := by decide
  have h9 : lambertPrefix 9 = 431800 := by decide
  have h10 : lambertPrefix 10 = 4431653 := by decide
  have ha : lambertCoeff 10 = 113653 := by decide
  have hc : coeff 10 = 55 := by
    norm_num [coeff, coeffRow, CongruencePreservingCarry.carry, y, scaledSumQ,
      Finset.sum_range_succ, Nat.factorial, h3, h4, h5, h6, h7, h8, h9, h10, ha]
  rw [hc]
  norm_num

#print axioms rational_twice_prime_not_congruent
#print axioms irrational_of_frequent_twice_prime_congruence
#print axioms irrational_of_twice_prime_congruences
#print axioms finite_inheritance_failure
#print axioms twice_prime_congruence_iff_carry_dvd

end CarriedTwicePrimeCriterion
