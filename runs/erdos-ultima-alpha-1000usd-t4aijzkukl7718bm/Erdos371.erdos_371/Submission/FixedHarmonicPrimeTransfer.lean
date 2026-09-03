import Submission.ApproximateHarmonicPrimeTransfer

/-! Actual prime comparison transfer using a single fixed finite label
sequence, independent of the endpoint. No prime-gap cancellation is assumed. -/
namespace Erdos371
open Finset Filter FiniteInformation BlockPrimes EntropyScales
open scoped Topology
set_option autoImplicit false

theorem localPrimeLabel_harmonic_prime_transfer (Q H₀ : ℕ) (hH₀ : 8 ≤ H₀)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∃ n < K,
      ∀ C : Fin (Q+1) → Fin (Q+1) → ℝ, (∀ a b, |C a b| ≤ 1) →
        |harmonicMean (N+1) (fun m => C (localPrimeLabel Q m) (localPrimeLabel Q (m+1)))-
          (∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicMean (N+1)
            (fun m => C (localPrimeLabel Q m) (localPrimeLabel Q (m+p)))) /
              (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨K,hK,htransfer⟩ := approximate_harmonic_prime_transfer (A := Fin (Q+1)) H₀ hH₀ ε hε
  refine ⟨K,hK,htransfer (localPrimeLabel Q) ?_⟩
  intro p hp
  convert localPrimeLabel_mul_mean_zero Q p hp using 1
  congr 1
  funext N
  congr 1
  funext n
  unfold labelDilationDefect
  split_ifs <;> rfl

/-- The adjacent true sign transfers to prime-gap correlations of ONE FIXED
finite sequence L_Q(m). Neither the labels nor the observable depend on N. -/
theorem actual_fixed_harmonic_prime_comparison_transfer
    (H₀ : ℕ) (hH₀ : 8 ≤ H₀) (ε : ℝ) (hε : 0 < ε) :
    ∃ Q > 0, ∃ K > 0, ∀ᶠ N : ℕ in atTop, ∃ n < K,
      |harmonicMean (N+1) factorSign-
        (∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicMean (N+1)
          (fun m => orderSkew (localPrimeLabel Q m) (localPrimeLabel Q (m+p)))) /
            (halfBlockPrimes (factorialScale H₀ n)).card| < ε := by
  obtain ⟨Q,hQ,happrox⟩ := localFactorSign_harmonic_approximation (ε/2) (by positivity)
  obtain ⟨K,hK,htransfer⟩ := localPrimeLabel_harmonic_prime_transfer Q H₀ hH₀ (ε/2) (by positivity)
  refine ⟨Q,hQ,K,hK,?_⟩
  filter_upwards [happrox Q le_rfl,htransfer] with N happrox htransfer
  obtain ⟨n,hn,hscale⟩ := htransfer
  refine ⟨n,hn,?_⟩
  have he := (harmonicMean_abs_difference_le N factorSign (localFactorSign Q)).trans happrox
  have hs := hscale orderSkew orderSkew_abs_le
  let V := (∑ p ∈ halfBlockPrimes (factorialScale H₀ n), harmonicMean (N+1)
    (fun m => orderSkew (localPrimeLabel Q m) (localPrimeLabel Q (m+p)))) /
      (halfBlockPrimes (factorialScale H₀ n)).card
  change |harmonicMean (N+1) (localFactorSign Q)-V| < ε/2 at hs
  change |harmonicMean (N+1) factorSign-V| < ε
  exact (abs_sub_le (harmonicMean (N+1) factorSign)
    (harmonicMean (N+1) (localFactorSign Q)) V).trans_lt (by linarith)

#print axioms localPrimeLabel_harmonic_prime_transfer
#print axioms actual_fixed_harmonic_prime_comparison_transfer
end Erdos371
