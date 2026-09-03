import Submission.CarriedSquareCongruenceBarrier
import Submission.LambertDescendingCongruence

/-!
A conditional application of the descending-factorial congruence to the
actual small-tail carry. The required inheritance is NOT proved here.
This file does not settle Erdős 68.
-/

namespace CarriedOddDescendingCriterion

open Erdos68Development CongruencePreservingCarry CarriedRationalPrimePattern

lemma last_prime_before_odd_composite (n : ℕ) (hn : 11 ≤ n)
    (ho : n % 2 = 1) (hc : ¬n.Prime) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p + 1 < n ∧ n + 3 ≤ 2*p ∧
      ∀ m : ℕ, p < m → m ≤ n → ¬m.Prime := by
  obtain ⟨s, hs, hns, hs2⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ((n+1)/2) (by omega)
  have hseven : 7 ≤ s := by omega
  have hsodd := hs.eq_two_or_odd.resolve_left (by omega)
  have hslt : s < n := by
    by_contra h
    have hsn : s = n := by omega
    exact hc (hsn ▸ hs)
  let S := (Finset.range n).filter Nat.Prime
  have hsmem : s ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hslt, hs⟩
  let p := S.max' ⟨s, hsmem⟩
  have hpmem : p ∈ S := Finset.max'_mem _ _
  have hsp : s ≤ p := Finset.le_max' S s hsmem
  have hpp : p.Prime := (Finset.mem_filter.mp hpmem).2
  have hpn : p < n := Finset.mem_range.mp (Finset.mem_filter.mp hpmem).1
  have hpodd := hpp.eq_two_or_odd.resolve_left (by omega)
  refine ⟨p, hpp, by omega, by omega, by omega, ?_⟩
  intro m hpm hmn hmp
  have hmlt : m < n := by
    by_contra h
    have he : m = n := by omega
    exact hc (he ▸ hmp)
  have hmmem : m ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_range]
    exact ⟨hmlt, hmp⟩
  have hmp' : m ≤ p := Finset.le_max' S m hmmem
  omega

lemma rational_coeff_in_composite_run (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (p n : ℕ)
    (hp : p.Prime) (hp5 : 5 ≤ p) (hden : q.den ≤ p-1)
    (hpn : p+1 < n) (hnp : n+2 ≤ 2*p)
    (hgap : ∀ m : ℕ, p < m → m ≤ n → ¬m.Prime) :
    coeff n = 1+((n : ℤ)-1)*(2*(p : ℤ)-n) := by
  have hstart := rational_prime_successor q hq p hp hp5 hden
  have hb := descending_block (integerTail q) p (n-p-1) hp5 (by omega) hstart
    (fun i hi => integerTail_nonprime_bounds q hq (p+1+i) (by omega) (by omega)
      (hgap _ (by omega) (by omega)))
    (fun i hi => integerTail_congruence q hq (p+1+i) (by omega) (by omega))
  have hprev : integerTail q (n-1) = 2*(p : ℤ)-n := by
    have h := hb (n-p-2) (by omega)
    rw [show p+1+(n-p-2) = n-1 by omega] at h
    omega
  have hnext : integerTail q n = 2*(p : ℤ)-1-n := by
    have h := hb (n-p-1) le_rfl
    rw [show p+1+(n-p-1) = n by omega] at h
    omega
  have he := integerTail_succ q hq (n-1) (by omega)
  rw [show n-1+1 = n by omega, hprev, hnext] at he
  rw [Nat.cast_sub (show 1 ≤ n by omega)] at he
  push_cast at he
  nlinarith

/-- With the actual carry's linear bounds at every composite, rationality
would prevent inheritance at every sufficiently late odd composite. -/
theorem rational_odd_composite_not_congruent (q : ℚ)
    (hq : (∑' k : ℕ, term k) = (q : ℝ)) (n : ℕ)
    (hn : 2*q.den+11 ≤ n) (ho : n % 2 = 1) (hc : ¬n.Prime) :
    ¬((n : ℤ)-1)*((n : ℤ)-2) ∣ coeff n-1 := by
  obtain ⟨p, hp, hp5, hpn, hnp, hgap⟩ :=
    last_prime_before_odd_composite n (by omega) ho hc
  have hcoef := rational_coeff_in_composite_run q hq p n hp hp5
    (by omega) hpn (by omega) hgap
  intro hd
  rw [hcoef, add_sub_cancel_left] at hd
  have hnz : (n : ℤ)-1 ≠ 0 := by omega
  have hk : (n : ℤ)-2 ∣ 2*(p : ℤ)-n := (mul_dvd_mul_iff_left hnz).mp hd
  have hz := Int.eq_zero_of_dvd_of_nonneg_of_lt
    (show 0 ≤ 2*(p : ℤ)-n by omega)
    (show 2*(p : ℤ)-n < (n : ℤ)-2 by omega) hk
  omega

/-- The original odd quadratic congruence survives exactly when this
combination of adjacent carries is divisible by its modulus. -/
theorem odd_congruence_iff_carry_transfer (n : ℕ) (hn : 5 ≤ n) (ho : Odd n) :
    ((n : ℤ)-1)*((n : ℤ)-2) ∣ coeff n-1 ↔
    ((n : ℤ)-1)*((n : ℤ)-2) ∣
      CongruencePreservingCarry.carry (n-3) -
        (n : ℤ)*CongruencePreservingCarry.carry (n-4) := by
  have ha : ((n : ℤ)-1)*((n : ℤ)-2) ∣ (lambertCoeff n : ℤ)-1 := by
    have h := Int.natCast_modEq_iff.mpr
      (LambertDescendingCongruence.lambertCoeff_modEq_odd_quadratic n (by omega) ho)
    have hd := Int.modEq_iff_dvd.mp h.symm
    simpa only [Nat.cast_mul, Nat.cast_sub (by omega : 1 ≤ n),
      Nat.cast_sub (by omega : 2 ≤ n), Nat.cast_one, Nat.cast_ofNat] using hd
  have he : coeff n = (lambertCoeff n : ℤ) +
      CongruencePreservingCarry.carry (n-3) -
      (n : ℤ)*CongruencePreservingCarry.carry (n-4) := by
    rw [coeff, if_neg (show ¬n < 4 by omega), coeffRow]
    rw [show n-4+4 = n by omega, show n-4+1 = n-3 by omega]
    have hcast : ((n-4 : ℕ) : ℤ)+4 = n := by omega
    rw [hcast]
  rw [he, show (lambertCoeff n : ℤ) + CongruencePreservingCarry.carry (n-3) -
      (n : ℤ)*CongruencePreservingCarry.carry (n-4) - 1 =
      ((lambertCoeff n : ℤ)-1) + (CongruencePreservingCarry.carry (n-3) -
        (n : ℤ)*CongruencePreservingCarry.carry (n-4)) by ring]
  exact dvd_add_right ha

/-- Arbitrarily late successful inheritances would suffice. Their existence
is not supplied by the original-coefficient congruence. -/
theorem irrational_of_frequent_odd_composite_congruence
    (h : ∀ M : ℕ, ∃ n ≥ M, n % 2 = 1 ∧ ¬n.Prime ∧
      ((n : ℤ)-1)*((n : ℤ)-2) ∣ coeff n-1) :
    Irrational (∑' k : ℕ, term k) := by
  rintro ⟨q, hq⟩
  obtain ⟨n, hn, ho, hc, hd⟩ := h (2*q.den+11)
  exact rational_odd_composite_not_congruent q hq.symm n hn ho hc hd

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
/-- The first odd composite already fails inheritance. These are different
coefficient sequences for the same sum, not a counterexample to the sum's
irrationality. -/
lemma finite_inheritance_failure :
    lambertCoeff 9 = 1681 ∧ coeff 9 = 49 ∧ ¬(56 : ℤ) ∣ coeff 9-1 := by
  have h3 : lambertPrefix 3 = 4 := by decide
  have h4 : lambertPrefix 4 = 23 := by decide
  have h5 : lambertPrefix 5 = 116 := by decide
  have h6 : lambertPrefix 6 = 807 := by decide
  have h7 : lambertPrefix 7 = 5650 := by decide
  have h8 : lambertPrefix 8 = 47791 := by decide
  have h9 : lambertPrefix 9 = 431800 := by decide
  have ha : lambertCoeff 9 = 1681 := by decide
  have hc : coeff 9 = 49 := by
    norm_num [coeff, coeffRow, CongruencePreservingCarry.carry, y, scaledSumQ,
      Finset.sum_range_succ, Nat.factorial, h3, h4, h5, h6, h7, h8, h9, ha]
  rw [ha, hc]
  norm_num

#print axioms finite_inheritance_failure

#print axioms rational_odd_composite_not_congruent
#print axioms odd_congruence_iff_carry_transfer
#print axioms irrational_of_frequent_odd_composite_congruence

end CarriedOddDescendingCriterion
