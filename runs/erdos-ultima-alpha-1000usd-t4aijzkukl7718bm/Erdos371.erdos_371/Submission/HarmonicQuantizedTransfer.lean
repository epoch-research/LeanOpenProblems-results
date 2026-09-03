import Submission.HarmonicStablePrimeTransfer
import Submission.PrimeLogQuantization

/-! Harmonic transfer specialized to the actual finite largest-prime-factor
labels. This is a transfer identity, not cancellation of the prime-gap mean. -/
namespace Erdos371
open Finset Filter FiniteInformation BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

theorem primeQuantLabel_harmonic_prime_transfer (Q H₀ : ℕ) (hH₀ : 8 ≤ H₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∃ n < K,
      ∀ C : Fin (Q+1) → Fin (Q+1) → ℝ, (∀ a b, |C a b| ≤ 1) →
        |harmonicMean (N+1) (fun m => C (primeQuantLabel Q (N+1) m) (primeQuantLabel Q (N+1) (m+1)))-
          (∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicMean (N+1)
            (fun m => C (primeQuantLabel Q (N+1) m) (primeQuantLabel Q (N+1) (m+p)))) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,htrans⟩ := stable_harmonic_prime_transfer (A := Fin (Q+1)) H₀ hH₀ ε hε
  let B := (range K).sup (factorialScale H₀)
  have hstable := (tendsto_add_atTop_nat 1).eventually (primeQuantLabel_eventually_mul Q B)
  refine ⟨K,hK,?_⟩
  filter_upwards [htrans,hstable] with N htrans hstable
  exact htrans (primeQuantLabel Q (N+1)) (fun p hp hpB m _ => hstable p hp hpB m)

#print axioms primeQuantLabel_harmonic_prime_transfer
end Erdos371
