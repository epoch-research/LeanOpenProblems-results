import Submission.SymmetricDivisorHyperbola
/-! Exact-type and axiom checks for symmetric divisor switching. -/

open Erdos821.HigherDivisors
open Nat Filter
open scoped Topology

example (H k n : ℕ) (hn : n < (H+1)^2) :
    tau (k+1) n = (lowZeta H ^ (k+1)) n +
      (k+1) * ∑ d ∈ n.divisors with H < n/d, tau k d :=
  tau_symmetric_hyperbola H k n hn

example (H k n : ℕ) (hn : n < (H+1)^2) :
    (k+1) * ∑ d ∈ n.divisors with H < n/d, tau k d ≤ tau (k+1) n :=
  symmetrized_divisor_sum_le H k n hn

example (H k n : ℕ) (hn : n ∉ Nat.smoothNumbers (H+1)) :
    (lowZeta H ^ k) n = 0 := lowZeta_pow_eq_zero_of_not_smooth H k n hn

example (k n : ℕ) : tau (2*k) n =
    2 * (∑ d ∈ n.divisors with d < n/d, tau k d * tau k (n/d)) +
      ∑ d ∈ n.divisors with d = n/d, tau k d * tau k (n/d) :=
  tau_balanced_hyperbola k n

example (θ c : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) (hc : 0 < c) :
    ∀ᶠ k : ℕ in atTop, (k+1 : ℝ)*θ^k/(k.factorial : ℝ) <
      c/((k+1).factorial : ℝ) :=
  eventually_symmetrized_coefficient_lt_factorial θ c hθ hθ1 hc

#print axioms lowZeta_add_highZeta
#print axioms arith_pow_congr_below
#print axioms lowZeta_pow_eq_tau
#print axioms highZeta_pow_eq_zero
#print axioms arith_natCast_mul_apply
#print axioms arith_sum_apply
#print axioms highZeta_pow_mul_eq_zero
#print axioms low_high_convolution
#print axioms tau_symmetric_hyperbola
#print axioms symmetrized_divisor_sum_le
#print axioms lowZeta_pow_eq_zero_of_large_prime
#print axioms lowZeta_pow_eq_zero_of_not_smooth
#print axioms tau_symmetric_hyperbola_of_not_smooth
#print axioms tau_balanced_hyperbola
#print axioms tendsto_symmetrized_factorial_coefficient
#print axioms eventually_symmetrized_coefficient_lt_factorial
