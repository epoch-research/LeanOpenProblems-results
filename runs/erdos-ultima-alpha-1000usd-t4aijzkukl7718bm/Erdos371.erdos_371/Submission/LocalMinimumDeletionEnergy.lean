import Submission.PrimeWinnerPrimeWeightedEnergy

/-! Exact accounting for deleting a strict local minimum. Even on the actual
largest-prime-factor prefix, this operation can increase weighted energy.
This is an obstruction to an auxiliary contraction, not a density disproof. -/
namespace Erdos371
open Finset

noncomputable def orderedPairSign (a b : ℕ) : ℝ := if a<b then 1 else -1

noncomputable def winnerEdgeContribution (a b p : ℕ) : ℝ :=
  if max a b=p then orderedPairSign a b else 0

lemma orderedPairSign_sq (a b : ℕ) : (orderedPairSign a b)^2=1 := by
  unfold orderedPairSign
  split_ifs <;> norm_num

/-- Replacing the two edges through a strict local minimum by their shortcut
adds one signed winner contribution at the smaller neighboring label. -/
lemma local_minimum_deletion_winner_update (a c b p : ℕ)
    (hca : c<a) (hcb : c<b) (hab : a≠b) :
    winnerEdgeContribution a b p-winnerEdgeContribution a c p-
      winnerEdgeContribution c b p =
        if min a b=p then orderedPairSign a b else 0 := by
  unfold winnerEdgeContribution orderedPairSign
  rcases lt_or_gt_of_ne hab with h | h
  · simp only [max_eq_right h.le,max_eq_left hca.le,max_eq_right hcb.le,
      min_eq_left h.le,h,hca.not_gt,hcb,if_true,if_false]
    split_ifs <;> ring
  · simp only [max_eq_left h.le,max_eq_left hca.le,max_eq_right hcb.le,
      min_eq_right h.le,h.not_gt,hca.not_gt,hcb,if_true,if_false]
    split_ifs <;> ring

lemma prime_weighted_energy_single_update (T : Finset ℕ) (S : ℕ → ℝ)
    (q : ℕ) (s : ℝ) (hq : q ∈ T) (hs : s^2=1) :
    (∑ p ∈ T, (p : ℝ)*(S p+(if q=p then s else 0))^2) =
      (∑ p ∈ T, (p : ℝ)*(S p)^2)+(q : ℝ)*(2*s*S q+1) := by
  have hrow (p : ℕ) : (p : ℝ)*(S p+(if q=p then s else 0))^2 =
      (p : ℝ)*(S p)^2+(if q=p then (q : ℝ)*(2*s*S q+1) else 0) := by
    by_cases h : q=p
    · subst p
      simp only [if_true]
      calc
        _ = (q : ℝ)*(S q)^2+(q : ℝ)*(2*s*S q+s^2) := by ring
        _ = _ := by rw [hs]
    · simp only [if_neg h,add_zero]
  simp_rw [hrow,sum_add_distrib]
  rw [sum_ite_eq,if_pos hq]

noncomputable def deleteLocalMinWinnerVector (S : ℕ → ℝ) (a c b p : ℕ) : ℝ :=
  S p-winnerEdgeContribution a c p-winnerEdgeContribution c b p+
    winnerEdgeContribution a b p

lemma deleteLocalMinWinnerVector_eq (S : ℕ → ℝ) (a c b p : ℕ)
    (hca : c<a) (hcb : c<b) (hab : a≠b) :
    deleteLocalMinWinnerVector S a c b p =
      S p+(if min a b=p then orderedPairSign a b else 0) := by
  have h := local_minimum_deletion_winner_update a c b p hca hcb hab
  unfold deleteLocalMinWinnerVector
  linarith

/-- The correction is not sign-definite. If the old sum at the affected
label is zero, deletion increases the energy by that positive label. -/
theorem local_minimum_deletion_energy_formula (T : Finset ℕ) (S : ℕ → ℝ)
    (a c b : ℕ) (hca : c<a) (hcb : c<b) (hab : a≠b) (hmin : min a b ∈ T) :
    (∑ p ∈ T, (p : ℝ)*(deleteLocalMinWinnerVector S a c b p)^2) =
      (∑ p ∈ T, (p : ℝ)*(S p)^2)+
        (min a b : ℕ)*(2*orderedPairSign a b*S (min a b)+1) := by
  simp_rw [deleteLocalMinWinnerVector_eq S a c b _ hca hcb hab]
  exact prime_weighted_energy_single_update T S (min a b) (orderedPairSign a b)
    hmin (orderedPairSign_sq a b)

private lemma small_prime_factor_values :
    Nat.maxPrimeFac 2=2 ∧ Nat.maxPrimeFac 3=3 ∧ Nat.maxPrimeFac 4=2 ∧ Nat.maxPrimeFac 5=5 := by
  decide +kernel

lemma primeWinnerSum_three_five_zero : primeWinnerSum 3 5=0 := by
  obtain ⟨h2,h3,h4,h5⟩ := small_prime_factor_values
  norm_num [primeWinnerSum,sum_filter,sum_range_succ,primeWinner,factorSign,predicateSign,
    h2,h3,h4,h5]

lemma primeWinnerPrimeWeightedEnergy_five : primeWinnerPrimeWeightedEnergy 5=8 := by
  obtain ⟨h2,h3,h4,h5⟩ := small_prime_factor_values
  have hlabels : primeWinnerLabels 5={1,2,3,5} := by decide +kernel
  norm_num [primeWinnerPrimeWeightedEnergy,hlabels,primeWinnerSum,sum_filter,sum_range_succ,
    primeWinner,factorSign,predicateSign,h2,h3,h4,h5]

/-- Delete the entry P(4) from the actual sequence P(0),...,P(5). The
shortcut replaces the edges P(3)->P(4)->P(5) by P(3)->P(5). -/
noncomputable def primeWeightedEnergy_delete_four_from_five : ℝ :=
  ∑ p ∈ primeWinnerLabels 5, (p : ℝ)*
    (deleteLocalMinWinnerVector (fun q => primeWinnerSum q 5)
      (Nat.maxPrimeFac 3) (Nat.maxPrimeFac 4) (Nat.maxPrimeFac 5) p)^2

lemma primeWeightedEnergy_delete_four_from_five_eq :
    primeWeightedEnergy_delete_four_from_five=11 := by
  obtain ⟨h2,h3,h4,h5⟩ := small_prime_factor_values
  have hmin : min 3 5 ∈ primeWinnerLabels 5 := by decide +kernel
  have h := local_minimum_deletion_energy_formula (primeWinnerLabels 5)
    (fun q => primeWinnerSum q 5) 3 2 5 (by decide) (by decide) (by decide) hmin
  change (∑ p ∈ primeWinnerLabels 5, (p : ℝ)*
      (deleteLocalMinWinnerVector (fun q => primeWinnerSum q 5) 3 2 5 p)^2) =
        primeWinnerPrimeWeightedEnergy 5+_ at h
  norm_num only [Nat.min_eq_left (by decide : 3≤5),primeWinnerSum_three_five_zero,
    primeWinnerPrimeWeightedEnergy_five,orderedPairSign] at h
  norm_num at h
  simpa only [primeWeightedEnergy_delete_four_from_five,h3,h4,h5] using h

/-- The deleted entry really is a strict local minimum, yet energy rises
from 8 to 11. This is not a counterexample to Erdős 371. -/
theorem actual_local_minimum_deletion_increases_weighted_energy :
    (Nat.maxPrimeFac 4<Nat.maxPrimeFac 3 ∧ Nat.maxPrimeFac 4<Nat.maxPrimeFac 5) ∧
      primeWinnerPrimeWeightedEnergy 5 < primeWeightedEnergy_delete_four_from_five := by
  obtain ⟨h2,h3,h4,h5⟩ := small_prime_factor_values
  rw [h3,h4,h5,primeWinnerPrimeWeightedEnergy_five,primeWeightedEnergy_delete_four_from_five_eq]
  norm_num

#print axioms local_minimum_deletion_energy_formula
#print axioms actual_local_minimum_deletion_increases_weighted_energy
end Erdos371
