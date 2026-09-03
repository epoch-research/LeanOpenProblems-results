import Submission.PrimeReflection

/-! A directed cycle in the actual large-prime comparison flow. This is
only a finite obstruction to an acyclicity argument, not a density
counterexample or an asymptotic lower bound. -/

namespace Erdos371

/-- Three comparisons below 66 form a directed cycle. Every label exceeds
the square root of the common endpoint, so this is not a small-label effect. -/
theorem large_prime_flow_cycle :
    Nat.maxPrimeFac 33 = 11 ∧ Nat.maxPrimeFac 34 = 17 ∧
    Nat.maxPrimeFac 51 = 17 ∧ Nat.maxPrimeFac 52 = 13 ∧
    Nat.maxPrimeFac 65 = 13 ∧ Nat.maxPrimeFac 66 = 11 ∧
    66 < 11^2 ∧ 66 < 13^2 ∧ 66 < 17^2 := by
  decide +kernel

/-- The cycle survives subtracting the opposite orientations in the same
prefix; it is a cycle of signed arithmetic flow, not just of raw edges. -/
theorem large_prime_net_flow_cycle :
    bilinearCount 66 11 17 = 1 ∧ bilinearCount 66 17 11 = 0 ∧
    bilinearCount 66 17 13 = 1 ∧ bilinearCount 66 13 17 = 0 ∧
    bilinearCount 66 13 11 = 1 ∧ bilinearCount 66 11 13 = 0 := by
  decide +kernel

#print axioms large_prime_flow_cycle
#print axioms large_prime_net_flow_cycle

end Erdos371
