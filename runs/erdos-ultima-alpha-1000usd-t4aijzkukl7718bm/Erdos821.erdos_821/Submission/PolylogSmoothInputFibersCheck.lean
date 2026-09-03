import Submission.PolylogSmoothInputFibers

/-! Exact-type checks and permitted-axiom audit for polylogarithmic inputs. -/

open Nat Filter
namespace Erdos821

example (γ : ℝ) (hγ : γ<1036568/2000001) (N : ℕ) :
    ∃ (n : ℕ) (F : Finset ℕ), N<n ∧ (n : ℝ)^γ < F.card ∧
      ∀ m ∈ F, Squarefree m ∧ totient m=n ∧
        ∀ p ∈ m.primeFactors,
          (p : ℝ) ≤ (4*Real.log (n : ℝ))^(2000001/963433 : ℝ) :=
  wide_block_polylog_input_fibers γ hγ N

#print axioms dyadic_card_le_four_log_output
#print axioms polylog_input_fibers_of_general_density
#print axioms polylog_input_fibers_of_eventual_polynomial_count
#print axioms wide_block_polylog_input_fibers

end Erdos821
