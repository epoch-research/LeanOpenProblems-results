import Submission.ArithmeticReduction

/-! An exact finite lower bound, used only to subtract an early raw charge. -/
namespace Erdos7NoFiveRawPrefix
open Erdos7No23Sieve
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000

def primes : List ℕ := (List.range 2504).filter (fun p =>
  decide (7 ≤ p) && @decide (Nat.Prime p) (Nat.decidablePrime' p))

lemma raw_lower : (387/200 : ℚ) < (primes.foldl rationalStep (5,1/4)).2 := by
  decide +kernel

lemma pairwise_primes : primes.Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

lemma budget_lower : (387/200 : ℚ) < 1/4+5*budgetCost primes.toFinset := by
  have h := raw_lower
  rw [rationalFold_eq primes pairwise_primes] at h
  exact h

#print axioms budget_lower
end Erdos7NoFiveRawPrefix
