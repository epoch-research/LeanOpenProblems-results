import Submission.Spec
import Submission.LocalRootUpper

/-! A concrete limitation of modular-density upper bounds: the actual cubic
representation count has power peaks despite its subpolynomial normalized
congruence densities. This is not a disproof of the original conjecture. -/
namespace Erdos322Research.LocalDensityInsufficient
noncomputable section
open LocalPeakCounting LocalRootUpper

/-- The completed local upper estimate and cubic power peaks hold simultaneously. -/
theorem cubic_local_bounds_and_exact_peaks :
    (∀ ε : ℝ, 0 < ε → ∃ C > (0 : ℝ), ∀ q : ℕ,
      0 < q → q.Coprime 3 →
      (rootCount 3 q : ℝ) ≤ C*(q : ℝ)^ε*(q : ℝ)^2) ∧
    {n : ℕ | (n : ℝ)^(1/12 : ℝ) < Erdos322.representationCount 3 n}.Infinite := by
  constructor
  · intro ε hε
    exact normalized_density_subpolynomial 3 (by omega) ε hε
  · exact Erdos322.cubic_exponent_one_twelfth

/-- Thus this local condition alone cannot rule out power peaks at every degree. -/
theorem not_local_implies_no_exact_peaks : ¬ (∀ k : ℕ, 3 ≤ k →
    (∀ ε : ℝ, 0 < ε → ∃ C > (0 : ℝ), ∀ q : ℕ,
      0 < q → q.Coprime k →
      (rootCount k q : ℝ) ≤ C*(q : ℝ)^ε*(q : ℝ)^(k-1)) →
    ∀ c : ℝ, 0 < c →
      {n : ℕ | (n : ℝ)^c < Erdos322.representationCount k n}.Finite) := by
  intro h
  have hlocal := cubic_local_bounds_and_exact_peaks.1
  have hfinite := h 3 (by omega) hlocal (1/12) (by norm_num)
  exact cubic_local_bounds_and_exact_peaks.2 hfinite

end
end Erdos322Research.LocalDensityInsufficient
