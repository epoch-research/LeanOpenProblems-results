import Submission.PrimeWinnerEnergyIncrement

/-! Exact separation of adjacent cancellation from the nonadjacent part of
prime-winner energy. No estimate on the nonadjacent signed sum is assumed. -/

namespace Erdos371
open Finset

lemma same_adjacent_winner_sign_product (n : ℕ)
    (hw : primeWinner n = primeWinner (n+1)) :
    factorSign (n+1)*factorSign n = -1 := by
  by_cases h1 : Nat.maxPrimeFac n < Nat.maxPrimeFac (n+1)
  · by_cases h2 : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac ((n+1)+1)
    · have he : Nat.maxPrimeFac (n+1) = Nat.maxPrimeFac ((n+1)+1) := by
        simpa only [primeWinner,max_eq_right h1.le,max_eq_right h2.le] using hw
      exact (h2.ne he).elim
    · simp [factorSign,predicateSign,h1,h2]
  · by_cases h2 : Nat.maxPrimeFac (n+1) < Nat.maxPrimeFac ((n+1)+1)
    · simp [factorSign,predicateSign,h1,h2]
    · have he : Nat.maxPrimeFac n = Nat.maxPrimeFac (n+1) := by
        simpa only [primeWinner,max_eq_left (not_lt.mp h1),
          max_eq_left (not_lt.mp h2)] using hw
      exact ((consecutive_maxPrimeFac_ne n) he.symm).elim

noncomputable def adjacentWinnerCount (N : ℕ) : ℕ :=
  ((range N).filter fun n => 0 < n ∧ primeWinner (n-1) = primeWinner n).card

noncomputable def primeWinnerNonadjacentCrossSum (N : ℕ) : ℝ :=
  ∑ n ∈ range N, ∑ m ∈ range (n-1),
    if primeWinner m = primeWinner n then factorSign n*factorSign m else 0

private lemma cross_row_adjacent_split (n : ℕ) :
    (∑ m ∈ range n, if primeWinner m = primeWinner n then
      factorSign n*factorSign m else 0) =
    (∑ m ∈ range (n-1), if primeWinner m = primeWinner n then
      factorSign n*factorSign m else 0) -
    (if 0 < n ∧ primeWinner (n-1) = primeWinner n then (1 : ℝ) else 0) := by
  cases n with
  | zero => simp
  | succ n =>
    simp only [Nat.add_sub_cancel,sum_range_succ,
      Nat.zero_lt_succ,true_and]
    by_cases hw : primeWinner n = primeWinner (n+1)
    · rw [if_pos hw,if_pos hw,same_adjacent_winner_sign_product n hw]
      ring
    · rw [if_neg hw,if_neg hw]
      ring

/-- Adjacent matching winners contribute exactly minus one per occurrence;
all nonadjacent matching winners remain in the signed remainder. -/
theorem primeWinnerCrossSum_adjacent_split (N : ℕ) :
    primeWinnerCrossSum N = primeWinnerNonadjacentCrossSum N-adjacentWinnerCount N := by
  rw [primeWinnerCrossSum_pair_formula]
  simp_rw [cross_row_adjacent_split,sum_sub_distrib]
  congr 1
  simp [adjacentWinnerCount]

/-- Exact energy identity after the automatic adjacent cancellations. -/
theorem primeWinnerEnergy_nonadjacent_formula (N : ℕ) :
    primeWinnerEnergy N = (N : ℝ)-2*adjacentWinnerCount N+
      2*primeWinnerNonadjacentCrossSum N := by
  rw [primeWinnerEnergy_eq_diagonal_add_cross,primeWinnerCrossSum_adjacent_split]
  ring

/-- A precise remaining one-sided inequality for the candidate E(N)<=N.
Neither side of this equivalence is asserted for all N. -/
theorem primeWinnerEnergy_le_diagonal_iff_nonadjacent (N : ℕ) :
    primeWinnerEnergy N ≤ N ↔
      primeWinnerNonadjacentCrossSum N ≤ adjacentWinnerCount N := by
  rw [primeWinnerEnergy_nonadjacent_formula]
  constructor <;> intro h <;> linarith

#print axioms same_adjacent_winner_sign_product
#print axioms primeWinnerCrossSum_adjacent_split
#print axioms primeWinnerEnergy_nonadjacent_formula
#print axioms primeWinnerEnergy_le_diagonal_iff_nonadjacent

end Erdos371
