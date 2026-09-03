import Submission.Explore

/-! A finite check of a proposed dyadic branch-pruning argument.
This is not a counterexample to the density conjecture. -/

namespace Erdos371

lemma dyadic_cancellation_can_reappear :
    ¬ factorBetween 2 ∧
      factorSign 4 + factorSign 5 = 0 ∧
      (∑ j ∈ Finset.range 4, factorSign (4 * 2 + j)) = 2 := by
  have h2 : Nat.maxPrimeFac 2 = 2 := by decide +kernel
  have h3 : Nat.maxPrimeFac 3 = 3 := by decide +kernel
  have h4 : Nat.maxPrimeFac 4 = 2 := by decide +kernel
  have h5 : Nat.maxPrimeFac 5 = 5 := by decide +kernel
  have h6 : Nat.maxPrimeFac 6 = 3 := by decide +kernel
  have h8 : Nat.maxPrimeFac 8 = 2 := by decide +kernel
  have h9 : Nat.maxPrimeFac 9 = 3 := by decide +kernel
  have h10 : Nat.maxPrimeFac 10 = 5 := by decide +kernel
  have h11 : Nat.maxPrimeFac 11 = 11 := by decide +kernel
  have h12 : Nat.maxPrimeFac 12 = 3 := by decide +kernel
  norm_num [factorBetween, factorSign, predicateSign, Finset.sum_range_succ,
    h2, h3, h4, h5, h6, h8, h9, h10, h11, h12]

#print axioms dyadic_cancellation_can_reappear
end Erdos371
