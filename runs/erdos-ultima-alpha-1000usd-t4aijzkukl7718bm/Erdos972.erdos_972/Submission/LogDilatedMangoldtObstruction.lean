import Submission.DilatedMangoldtObstruction
import Submission.CesaroLogarithmicMean

/-! The failure of a direct unbounded Kátai-type inference persists under
logarithmic averaging. These are diagnostic results, not a settlement of
Erdős 972. -/
namespace Erdos972LogDilatedMangoldtObstruction

open Finset Filter ArithmeticFunction
open scoped Topology ArithmeticFunction.Moebius
open Erdos972DilatedMangoldtObstruction Erdos972CesaroLogarithmicMean

/-- Reciprocal weighting and logarithmic normalization do not change the
vanishing of the distinct-prime dilated Mangoldt correlation. -/
theorem distinct_prime_dilates_log_mean {r s : ℕ}
    (hr : r.Prime) (hs : s.Prime) (hrs : r ≠ s) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, Λ (r*n) * Λ (s*n) / n) / Real.log N)
      atTop (𝓝 0) :=
  cesaro_Ioc_to_logarithmic (distinct_prime_dilates_mean_tendsto hr hs hrs)

/-- Despite the preceding vanishing, Mangoldt retains logarithmic correlation
minus one with Möbius. -/
theorem moebius_mangoldt_log_mean :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Ioc 0 N, (μ n : ℝ) * Λ n / n) / Real.log N)
      atTop (𝓝 (-1)) :=
  cesaro_Ioc_to_logarithmic moebius_mangoldt_mean_tendsto

/-- Explicitly refutes an unrestricted extension of the bounded-function
criterion. A prime-output-specific theorem would need further hypotheses. -/
theorem not_unrestricted_log_dilation_criterion :
    ¬ (∀ f : ℕ → ℝ,
      (∀ r s : ℕ, r.Prime → s.Prime → r ≠ s →
        Tendsto (fun N : ℕ =>
          (∑ n ∈ Ioc 0 N, f (r*n) * f (s*n) / n) / Real.log N)
          atTop (𝓝 0)) →
      Tendsto (fun N : ℕ =>
        (∑ n ∈ Ioc 0 N, (μ n : ℝ) * f n / n) / Real.log N)
        atTop (𝓝 0)) := by
  intro h
  have hz := h Λ (fun r s hr hs hrs => distinct_prime_dilates_log_mean hr hs hrs)
  have he := tendsto_nhds_unique moebius_mangoldt_log_mean hz
  norm_num at he

#print axioms distinct_prime_dilates_log_mean
#print axioms moebius_mangoldt_log_mean
#print axioms not_unrestricted_log_dilation_criterion

end Erdos972LogDilatedMangoldtObstruction
