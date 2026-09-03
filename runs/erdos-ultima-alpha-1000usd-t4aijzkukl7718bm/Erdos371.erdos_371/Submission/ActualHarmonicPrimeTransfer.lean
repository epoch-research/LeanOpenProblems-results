import Submission.HarmonicQuantizedTransfer
import Submission.HarmonicComparisonApproximation

/-! An unconditional transfer from the actual adjacent comparison bias to
prime-gap skew correlations of actual finite largest-prime-factor labels.
The latter signed mean is NOT evaluated in this file. -/
namespace Erdos371
open Finset Filter FiniteInformation BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

/-- Unlike the natural-average transfer, the adjacent mean on the left uses
the full endpoint N+1 for every prime in the selected block. -/
theorem actual_harmonic_prime_comparison_transfer
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q > 0, ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∃ n < K,
      |harmonicMean (N+1) factorSign-
        (∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicMean (N+1)
          (fun m => orderSkew (primeQuantLabel Q (N+1) m) (primeQuantLabel Q (N+1) (m+p)))) /
            (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨Q,hQ,happrox⟩ := quantFactorSign_harmonic_approximation (ε/2) (by positivity)
  obtain ⟨K,hK,htransfer⟩ := primeQuantLabel_harmonic_prime_transfer Q H₀ hH₀ (ε/2) (by positivity)
  refine ⟨Q,hQ,K,hK,?_⟩
  filter_upwards [happrox,htransfer] with N happrox htransfer
  obtain ⟨n,hn,hscale⟩ := htransfer
  refine ⟨n,hn,?_⟩
  have he := (harmonicMean_abs_difference_le N factorSign (quantFactorSign Q (N+1))).trans
    (happrox Q le_rfl)
  have hs := hscale orderSkew orderSkew_abs_le
  let V := (∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicMean (N+1)
    (fun m => orderSkew (primeQuantLabel Q (N+1) m) (primeQuantLabel Q (N+1) (m+p)))) /
      (halfBlockPrimes (factorialScale H₀ n)).card
  change |harmonicMean (N+1) (quantFactorSign Q (N+1))-V| < ε/2 at hs
  change |harmonicMean (N+1) factorSign-V| < ε
  exact (abs_sub_le (harmonicMean (N+1) factorSign)
    (harmonicMean (N+1) (quantFactorSign Q (N+1))) V).trans_lt (by linarith)

#print axioms actual_harmonic_prime_comparison_transfer
end Erdos371
