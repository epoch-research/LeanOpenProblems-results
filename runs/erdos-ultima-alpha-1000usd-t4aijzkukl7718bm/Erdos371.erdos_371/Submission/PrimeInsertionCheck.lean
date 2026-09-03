import Submission.PrefixBalanceObstruction

/-! A finite check on the prime-insertion strategy. This refutes only the
proposed two-unit per-insertion bound, not the density conjecture. -/
namespace Erdos371
open Finset

lemma insertion_seven_prefix_counts :
    ((range 49).filter fun n => cutoffPrime 30 n < cutoffPrime 30 (n+1)).card = 25 ∧
    ((range 49).filter fun n => cutoffPrime 30 (n+1) < cutoffPrime 30 n).card = 24 ∧
    ((range 49).filter fun n => cutoffPrime 210 n < cutoffPrime 210 (n+1)).card = 27 ∧
    ((range 49).filter fun n => cutoffPrime 210 (n+1) < cutoffPrime 210 n).card = 22 := by
  decide +kernel

lemma insertion_seven_signed_increment :
    ((((range 49).filter fun n => cutoffPrime 210 n < cutoffPrime 210 (n+1)).card : ℤ) -
      ((range 49).filter fun n => cutoffPrime 210 (n+1) < cutoffPrime 210 n).card) -
    ((((range 49).filter fun n => cutoffPrime 30 n < cutoffPrime 30 (n+1)).card : ℤ) -
      ((range 49).filter fun n => cutoffPrime 30 (n+1) < cutoffPrime 30 n).card) = 4 := by
  rw [insertion_seven_prefix_counts.1,insertion_seven_prefix_counts.2.1,
    insertion_seven_prefix_counts.2.2.1,insertion_seven_prefix_counts.2.2.2]
  norm_num

/-- Rational version of the finite-cutoff comparison, with zero for ties. -/
def cutoffPrimeSkewRat (M n : ℕ) : ℚ :=
  if cutoffPrime M n < cutoffPrime M (n+1) then 1
  else if cutoffPrime M (n+1) < cutoffPrime M n then -1 else 0

/-- Inserting 13 into the initial prime cutoff decreases this harmonic
prefix. Thus prime insertion is not monotone even for the weighted sums.
This is an auxiliary finite obstruction, not a density counterexample. -/
lemma insertion_thirteen_harmonic_increment :
    (∑ n ∈ range 40, (cutoffPrimeSkewRat 30030 n-cutoffPrimeSkewRat 2310 n)/(n : ℚ)) =
      -23/650 := by
  decide +kernel

#print axioms insertion_thirteen_harmonic_increment

#print axioms insertion_seven_signed_increment
end Erdos371
