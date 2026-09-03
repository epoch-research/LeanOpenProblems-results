import FormalConjecturesUtil
import Submission.PeriodEnergyObstruction

/-! A finite obstruction to bounding the total cutoff discrepancy by twice
  the number of selected primes. This is not a disproof of Erdős 371. -/

namespace Erdos371InitialPeriodTotalObstruction

open Erdos371PeriodEnergyObstruction

def initialPrimes : Finset ℕ := {2,3,5,7,11,13}

def total (s : Finset ℕ) (N : ℕ) : ℤ :=
  ∑ n ∈ Finset.range N,sign s n

lemma initialPrimes_eq : initialPrimes = Nat.primesBelow 14 := by decide +kernel

lemma initialPrimes_card : initialPrimes.card=6 := by decide +kernel

set_option maxRecDepth 200000 in
set_option maxHeartbeats 12000000 in
lemma total_initial : total initialPrimes 9373=13 := by
  have h0 : (∑ n ∈ Finset.range 2500,sign initialPrimes n)=2 := by decide +kernel
  have h1 : (∑ n ∈ Finset.range 2500,sign initialPrimes (2500+n))=4 := by decide +kernel
  have h2 : (∑ n ∈ Finset.range 2500,sign initialPrimes (5000+n))= -6 := by decide +kernel
  have h3 : (∑ n ∈ Finset.range 1873,sign initialPrimes (7500+n))=13 := by decide +kernel
  have h4 := Finset.sum_range_add (sign initialPrimes) 2500 2500
  have h5 := Finset.sum_range_add (sign initialPrimes) 5000 2500
  have h6 := Finset.sum_range_add (sign initialPrimes) 7500 1873
  norm_num only [Nat.reduceAdd] at h4 h5 h6
  unfold total
  omega

/-- Even initial segments do not admit this proposed finite bound. -/
theorem twice_selected_card_bound_fails :
    ¬∀ K N : ℕ, |total (Nat.primesBelow K) N|≤2*((Nat.primesBelow K).card:ℤ) := by
  intro h
  have hh := h 14 9373
  rw [← initialPrimes_eq,total_initial,initialPrimes_card] at hh
  norm_num at hh

end Erdos371InitialPeriodTotalObstruction

#print axioms Erdos371InitialPeriodTotalObstruction.total_initial
#print axioms Erdos371InitialPeriodTotalObstruction.twice_selected_card_bound_fails
