import Submission.NoFiveRawTheory
import Submission.NoFiveRawPrefix

/-! A checked subtraction of the early raw second-moment charge. -/
namespace Erdos7NoFiveSaving
open scoped BigOperators
open Erdos7NoFiveScalar Erdos7NoFiveRaw
set_option maxHeartbeats 100000000
set_option maxRecDepth 500000

lemma initial_bound : (states 0).eval 1 ≤ (905/1000 : ℚ) := by decide +kernel

lemma prefix_set : Finset.univ.image Erdos7NoFiveScalar.primes =
    {3} ∪ Erdos7NoFiveRawPrefix.primes.toFinset := by
  decide +kernel

lemma saving_certificate : (states 0).eval 1 + (103/100 : ℚ) <
    costC (Finset.univ.image Erdos7NoFiveScalar.primes) := by
  rw [prefix_set,costC_three_union _ (by
    intro p hp
    have hh := (List.mem_filter.mp (List.mem_toFinset.mp hp)).2
    have h7 : 7 ≤ p := by
      by_contra h
      simp only [decide_eq_false h, Bool.false_and] at hh
      contradiction
    omega)]
  linarith [initial_bound,Erdos7NoFiveRawPrefix.budget_lower]

#print axioms saving_certificate
end Erdos7NoFiveSaving
