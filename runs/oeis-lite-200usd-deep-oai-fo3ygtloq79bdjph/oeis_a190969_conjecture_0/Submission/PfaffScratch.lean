import FormalConjectures.Util.ProblemImports

open Finset Nat Polynomial
open scoped BigOperators

namespace Polynomial

lemma shiftedLegendre_pfaff_test (n : ℕ) :
    (shiftedLegendre n : ℤ[X]) =
      ∑ k ∈ range (n+1), C ((n.choose k : ℤ)^2) * (-X)^k * (1 - X)^(n-k) := by
  ext m
  rw [coeff_shiftedLegendre]
  rw [finset_sum_coeff]
  -- coefficient RHS is sum over k≤m? try simp
  simp_rw [coeff_C_mul, coeff_mul]
  sorry

end Polynomial
