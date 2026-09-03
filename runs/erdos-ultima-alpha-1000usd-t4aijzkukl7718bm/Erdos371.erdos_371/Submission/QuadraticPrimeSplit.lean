import Submission.DampedQuadratic

/-! Separating the quadratic cross-prime term at the hyperbola pq=N. -/
namespace Erdos371
open Finset

lemma primeFactors_eq_filter_primesBelow (N n : ℕ) (hn : 0 < n) (hnN : n ≤ N) :
    n.primeFactors = (N+1).primesBelow.filter (fun p => p ∣ n) := by
  ext p
  constructor
  · intro hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hd := Nat.dvd_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨Nat.mem_primesBelow.mpr ⟨by have := Nat.le_of_dvd hn hd; omega,hp'⟩,hd⟩
  · intro hp
    obtain ⟨hp,hd⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Nat.mem_primesBelow.mp hp).2,hd,hn.ne'⟩

lemma shortPrimePairSkew_eq_cross (N n : ℕ) (hn : 0 < n) (hnN : n+1 ≤ N) :
    shortPrimePairSkew N n =
      ∑ p ∈ n.primeFactors, ∑ q ∈ (n+1).primeFactors,
        if p*q ≤ N then (if p < q then (1 : ℝ) else -1) else 0 := by
  let P := (N+1).primesBelow
  have he (p q : ℕ) :
      (if p < q ∧ p*q ≤ N then pairIndicatorDifference p q n else 0) =
      (if p < q ∧ p*q ≤ N ∧ p ∣ n ∧ q ∣ n+1 then (1 : ℝ) else 0)-
      (if p < q ∧ p*q ≤ N ∧ q ∣ n ∧ p ∣ n+1 then (1 : ℝ) else 0) := by
    unfold pairIndicatorDifference
    split_ifs <;> simp_all
  have hs : shortPrimePairSkew N n =
      (∑ p ∈ P, ∑ q ∈ P, if p < q ∧ p*q ≤ N ∧ p ∣ n ∧ q ∣ n+1 then (1 : ℝ) else 0)-
      (∑ p ∈ P, ∑ q ∈ P, if p < q ∧ p*q ≤ N ∧ q ∣ n ∧ p ∣ n+1 then (1 : ℝ) else 0) := by
    unfold shortPrimePairSkew shortPrimePairs
    rw [sum_filter,sum_product]
    simp_rw [he,sum_sub_distrib]
    rfl
  rw [hs, sum_comm (f := fun p q => if p < q ∧ p*q ≤ N ∧ q ∣ n ∧ p ∣ n+1 then (1 : ℝ) else 0),
    ← sum_sub_distrib,primeFactors_eq_filter_primesBelow N n hn (by omega),
    primeFactors_eq_filter_primesBelow N (n+1) (by omega) hnN]
  rw [sum_filter]
  apply sum_congr rfl
  intro p hp
  have hpp := (Nat.mem_primesBelow.mp hp).2
  rw [← sum_sub_distrib]
  by_cases hpn : p ∣ n
  · rw [if_pos hpn,sum_filter]
    apply sum_congr rfl
    intro q hq
    by_cases hqn : q ∣ n+1
    · have hpq : p ≠ q := by
        intro he
        subst q
        exact hpp.not_dvd_one ((Nat.dvd_add_iff_right hpn).mpr hqn)
      simp only [hpn,hqn,and_true,Nat.mul_comm q p,if_true]
      rcases lt_or_gt_of_ne hpq with h | h <;> by_cases hN : p*q ≤ N <;>
        simp [h,not_lt.mpr h.le,hN]
    · simp [hqn]
  · simp [hpn]

lemma crossPrimeSkew_split (N n : ℕ) (hn : 0 < n) (hnN : n+1 ≤ N) :
    crossPrimeSkew n = shortPrimePairSkew N n+largeCrossPrimePairSkew N n := by
  rw [shortPrimePairSkew_eq_cross N n hn hnN]
  unfold crossPrimeSkew largeCrossPrimePairSkew largeCrossPrimePairs
  rw [sum_filter,sum_product,← sum_add_distrib]
  apply sum_congr rfl
  intro p hp
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro q hq
  by_cases h : p*q ≤ N
  · simp [h,not_lt.mpr h]
  · simp [h,lt_of_not_ge h]

/-- The short hyperbola has unconditionally vanishing mean. The entire
remaining quadratic contribution is a weighted comparison sign. -/
theorem dampedFactorSign_quadratic_split (N n : ℕ) (hn : 1 < n) (hnN : n+1 ≤ N) :
    dampedCoefficient 2 (fun p => if p ∣ n+1 then 1 else -1) (n*(n+1)).primeFactors =
      (n.primeFactors.card.choose 2 : ℝ)-(n+1).primeFactors.card.choose 2+
        shortPrimePairSkew N n+(largeCrossPrimePairs N n).card*factorSign n := by
  rw [dampedFactorSign_quadratic_coefficient n (by omega),crossPrimeSkew_split N n (by omega) hnN,
    largeCrossPrimePairSkew_eq N n hn hnN]
  ring

#print axioms shortPrimePairSkew_eq_cross
#print axioms dampedFactorSign_quadratic_split
end Erdos371
