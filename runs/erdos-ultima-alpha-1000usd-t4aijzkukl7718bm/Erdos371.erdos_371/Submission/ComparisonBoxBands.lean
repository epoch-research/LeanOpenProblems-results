import Submission.AllocationSmallBoxes
import Submission.UninflatedAllocationApproximation

/-! Two-sided box cutoffs for the comparison weights. The estimates below
are unsigned: they preserve mass but assert no cancellation of orientations. -/
namespace Erdos371
open Finset Filter RandomBins FiniteSieve
open scoped Topology
attribute [local instance] Classical.propDecidable

lemma primeDivisorCountIn_div_prime (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime)
    (p n : ℕ) (hp : p.Prime) (hd : p ∣ n) (hne : ∀ q ∈ S, q ≠ p) :
    primeDivisorCountIn S (n/p) = primeDivisorCountIn S n := by
  unfold primeDivisorCountIn
  congr 1
  apply filter_congr
  intro q hq
  constructor
  · intro h
    exact h.trans (Nat.div_dvd_of_dvd hd)
  · intro h
    rw [← Nat.mul_div_cancel' hd] at h
    rcases (hS q hq).dvd_mul.mp h with h | h
    · exact False.elim (hne q hq ((Nat.prime_dvd_prime_iff_eq (hS q hq) hp).mp h))
    · exact h

namespace RandomBins

noncomputable def primeAllocationBandRetention (K : ℕ) (Y X : ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a : PrimeAtomIndex n → Fin K =>
      ∀ c, Y ≤ (boxProduct (primePowerAtom n) a c : ℝ) ∧
        (boxProduct (primePowerAtom n) a c : ℝ) ≤ X),
    ∏ c, allocationWeight K (boxProduct (primePowerAtom n) a c)

lemma primeAllocationBandRetention_bounds (K : ℕ) (Y X : ℝ) (n : ℕ) :
    0 ≤ primeAllocationBandRetention K Y X n ∧
      primeAllocationBandRetention K Y X n ≤ primeAllocationRetention K X n := by
  have hw (a : PrimeAtomIndex n → Fin K) :
      0 ≤ ∏ c, allocationWeight K (boxProduct (primePowerAtom n) a c) := by
    apply prod_nonneg
    intro c hc
    unfold allocationWeight
    positivity
  constructor
  · exact sum_nonneg (fun a ha => hw a)
  · apply sum_le_sum_of_subset_of_nonneg
    · intro a ha
      exact mem_filter.mpr ⟨mem_univ _,fun c => ((mem_filter.mp ha).2 c).2⟩
    · intro a ha hnot
      exact hw a

lemma primeAllocationBandRetention_loss (K : ℕ) (Y X : ℝ) (n : ℕ) :
    primeAllocationRetention K X n-primeAllocationBandRetention K Y X n ≤
      smallBoxAllocationMass K Y n := by
  unfold primeAllocationRetention primeAllocationBandRetention smallBoxAllocationMass
  simp only [sum_filter,← sum_sub_distrib]
  apply sum_le_sum
  intro a ha
  let W := ∏ c, allocationWeight K (boxProduct (primePowerAtom n) a c)
  have hW : 0 ≤ W := by
    apply prod_nonneg
    intro c hc
    unfold allocationWeight
    positivity
  change (if ∀ c, (boxProduct (primePowerAtom n) a c : ℝ) ≤ X then W else 0) -
    (if ∀ c, Y ≤ (boxProduct (primePowerAtom n) a c : ℝ) ∧
      (boxProduct (primePowerAtom n) a c : ℝ) ≤ X then W else 0) ≤
    if ∃ c, (boxProduct (primePowerAtom n) a c : ℝ) < Y then W else 0
  by_cases hupper : ∀ c, (boxProduct (primePowerAtom n) a c : ℝ) ≤ X
  · by_cases hlower : ∀ c, Y ≤ (boxProduct (primePowerAtom n) a c : ℝ)
    · have hband : ∀ c, Y ≤ (boxProduct (primePowerAtom n) a c : ℝ) ∧
          (boxProduct (primePowerAtom n) a c : ℝ) ≤ X := fun c => ⟨hlower c,hupper c⟩
      have hnot : ¬∃ c, (boxProduct (primePowerAtom n) a c : ℝ) < Y := by
        rintro ⟨c,hc⟩
        exact (hlower c).not_gt hc
      simp only [if_pos hupper,if_pos hband,if_neg hnot,sub_self,le_refl]
    · have hnot : ¬∀ c, Y ≤ (boxProduct (primePowerAtom n) a c : ℝ) ∧
          (boxProduct (primePowerAtom n) a c : ℝ) ≤ X := fun h => hlower (fun c => (h c).1)
      push_neg at hlower
      simp only [if_pos hupper,if_neg hnot,if_pos hlower,sub_zero,le_refl]
  · have hnot : ¬∀ c, Y ≤ (boxProduct (primePowerAtom n) a c : ℝ) ∧
        (boxProduct (primePowerAtom n) a c : ℝ) ≤ X := fun h => hupper (fun c => (h c).2)
    simp only [if_neg hupper,if_neg hnot,sub_self]
    split_ifs
    · exact hW
    · exact le_rfl

end RandomBins

noncomputable def comparisonBandAllocationWeight (K N : ℕ) (η : ℝ) (n : ℕ) : ℝ :=
  primeAllocationBandRetention K ((N : ℝ)^η) (primeWinner n) (losingNumber n) *
    primeAllocationBandRetention K ((N : ℝ)^η) (primeWinner n)
      (winningNumber n / primeWinner n)

lemma comparisonBandAllocationWeight_bounds (K N : ℕ) (hK : 0 < K) (η : ℝ) (n : ℕ) :
    0 ≤ comparisonBandAllocationWeight K N η n ∧
      comparisonBandAllocationWeight K N η n ≤ comparisonAllocationWeight K N 0 n := by
  have hl := primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n) (losingNumber n)
  have hw := primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n)
    (winningNumber n/primeWinner n)
  unfold comparisonBandAllocationWeight comparisonAllocationWeight
  simp only [Real.rpow_zero,mul_one]
  exact ⟨mul_nonneg hl.1 hw.1,
    mul_le_mul hl.2 hw.2 hw.1 (primeAllocationRetention_mem_unit K hK _ _).1⟩

lemma comparisonBandAllocationWeight_loss (K N : ℕ) (hK : 0 < K) (η : ℝ) (n : ℕ) :
    comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n ≤
      smallBoxAllocationMass K ((N : ℝ)^η) (losingNumber n) +
        smallBoxAllocationMass K ((N : ℝ)^η) (winningNumber n/primeWinner n) := by
  have hl := primeAllocationRetention_mem_unit K hK (primeWinner n) (losingNumber n)
  have hw := primeAllocationRetention_mem_unit K hK (primeWinner n) (winningNumber n/primeWinner n)
  have hbl := primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n) (losingNumber n)
  have hbw := primeAllocationBandRetention_bounds K ((N : ℝ)^η) (primeWinner n) (winningNumber n/primeWinner n)
  have hdl := primeAllocationBandRetention_loss K ((N : ℝ)^η) (primeWinner n) (losingNumber n)
  have hdw := primeAllocationBandRetention_loss K ((N : ℝ)^η) (primeWinner n) (winningNumber n/primeWinner n)
  have h₁ := mul_nonneg (sub_nonneg.mpr hbl.2) (sub_nonneg.mpr hw.2)
  have h₂ := mul_nonneg (sub_nonneg.mpr hbw.2) (sub_nonneg.mpr (hbl.2.trans hl.2))
  unfold comparisonAllocationWeight comparisonBandAllocationWeight
  simp only [Real.rpow_zero,mul_one]
  nlinarith

lemma comparisonBandAllocationWeight_prime_count_bound (K N n : ℕ) (hK : 0 < K)
    (η α : ℝ) (S : Finset ℕ)
    (hS : ∀ q ∈ S, q.Prime ∧ (N : ℝ)^η ≤ q ∧ (q : ℝ) ≤ (N : ℝ)^α)
    (hn : 1 < n) (hpN : (N : ℝ)^α < primeWinner n) :
    comparisonAllocationWeight K N 0 n-comparisonBandAllocationWeight K N η n ≤
      (K : ℝ)*((1-1/(K : ℝ))^primeDivisorCountIn S n +
        (1-1/(K : ℝ))^primeDivisorCountIn S (n+1)) := by
  obtain ⟨hl,hw,hlN,hwN⟩ := comparison_numbers_bounds n hn
  obtain ⟨hp,hlp,hwp⟩ := comparison_numbers_prime_factors n hn
  have hd : primeWinner n ∣ winningNumber n := by
    rw [← hwp]
    exact Nat.maxPrimeFac_dvd
  have hq : 0 < winningNumber n/primeWinner n :=
    Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
  have hne : ∀ q ∈ S, q ≠ primeWinner n := by
    intro q hq he
    have h := (hS q hq).2.2
    rw [he] at h
    exact hpN.not_ge h
  have he := primeDivisorCountIn_div_prime S (fun q hq => (hS q hq).1)
    (primeWinner n) (winningNumber n) hp hd hne
  have h₁ := smallBoxAllocationMass_prime_count_bound K hK ((N : ℝ)^η) S
    (fun q hq => ⟨(hS q hq).1,(hS q hq).2.1⟩) (losingNumber n) (by omega)
  have h₂ := smallBoxAllocationMass_prime_count_bound K hK ((N : ℝ)^η) S
    (fun q hq => ⟨(hS q hq).1,(hS q hq).2.1⟩) (winningNumber n/primeWinner n) hq.ne'
  rw [he] at h₂
  have hb := (comparisonBandAllocationWeight_loss K N hK η n).trans (add_le_add h₁ h₂)
  have hs : (1-1/(K : ℝ))^primeDivisorCountIn S (losingNumber n) +
      (1-1/(K : ℝ))^primeDivisorCountIn S (winningNumber n) =
      (1-1/(K : ℝ))^primeDivisorCountIn S n + (1-1/(K : ℝ))^primeDivisorCountIn S (n+1) := by
    unfold losingNumber winningNumber
    split_ifs <;> ring
  rw [← mul_add,hs] at hb
  exact hb

#print axioms primeDivisorCountIn_div_prime
#print axioms primeAllocationBandRetention_loss
#print axioms comparisonBandAllocationWeight_prime_count_bound
end Erdos371
