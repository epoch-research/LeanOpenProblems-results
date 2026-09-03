import Submission.SquarefreeColoring

/-! Exact-type checks and permitted-axiom audit for squarefree colorings. -/

open Nat Filter
namespace Erdos821

example (C s : ℝ) (hC : 0≤C) (j n : ℕ) (hn : 0<n)
    (H : ∀ d ∈ n.divisors, (g d : ℝ) ≤ C*(d : ℝ)^s) :
    (coloredFiber (2^j) n : ℝ) ≤ C^(2^j)*(n : ℝ)^s*
      (n.divisors.card : ℝ)^(2^j-1) :=
  coloredFiber_two_pow_le_of_divisor_bound C s hC j n hn H

example (C s : ℝ) (hC : 0≤C) (F : Finset ℕ) (n j k : ℕ) (hn : 0<n)
    (hF : ∀ m ∈ F, Squarefree m ∧ totient m=n ∧ k ≤ m.primeFactors.card)
    (hcolor : C^(2^j)*(n : ℝ)^s*(n.divisors.card : ℝ)^(2^j-1) <
      (F.card : ℝ)*(2^j : ℝ)^k) :
    ∃ d ∈ n.divisors, C*(d : ℝ)^s < (g d : ℝ) :=
  exists_divisor_large_g_of_coloring C s hC F n j k hn hF hcolor

#print axioms mem_squarefreeFiber
#print axioms squarefreeFiber_card
#print axioms tau_squarefree
#print axioms coloredFiber_eq_color_sum
#print axioms coloredFiber_one
#print axioms squarefree_convolution_push_le
#print axioms coloredFiber_double_le
#print axioms finite_squarefree_fiber_color_lower
#print axioms coloredFiber_two_pow_le_of_divisor_bound
#print axioms coloredFiber_two_pow_le_of_power_bound
#print axioms finite_color_bound_of_g_power
#print axioms exists_divisor_large_g_of_coloring

end Erdos821
