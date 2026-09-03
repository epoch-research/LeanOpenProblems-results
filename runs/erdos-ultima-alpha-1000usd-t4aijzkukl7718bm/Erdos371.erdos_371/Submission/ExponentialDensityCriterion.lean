import Submission.ExponentialAbelian
import Submission.TailExplore

/-! An ordinary exponential-mean criterion equivalent to Erdős 371.
The exponential cancellation hypothesis is not established in this file. -/
namespace Erdos371
open Filter
open scoped Topology

/-- This uses ordinary exponential smoothing in the integer variable, not
Dirichlet-Abel smoothing or logarithmic averaging. -/
theorem density_of_exponential_sign_cancellation
    (hA : Tendsto (ExponentialWindow.exponentialMean factorSign)
      (𝓝[>] 0) (𝓝 0)) :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_signed_count]
  apply ExponentialWindow.cesaro_zero_of_exponential_zero factorSign _ hA
  intro n
  exact (by simpa only [Real.norm_eq_abs] using (factorSign_norm n).le)

/-- The ordinary exponential criterion is equivalent to the original
conjecture, not a consequence of the available logarithmic averages. -/
theorem density_iff_exponential_sign_cancellation :
    {n | Nat.maxPrimeFac (n+1) > Nat.maxPrimeFac n}.HasDensity (1/2) ↔
      Tendsto (ExponentialWindow.exponentialMean factorSign) (𝓝[>] 0) (𝓝 0) := by
  rw [density_iff_signed_count]
  simp_rw [← factorSign_sum_eq_signed_count]
  exact (ExponentialWindow.exponential_zero_iff_cesaro_zero factorSign
    (fun n => by simpa only [Real.norm_eq_abs] using (factorSign_norm n).le)).symm

#print axioms density_iff_exponential_sign_cancellation

#print axioms density_of_exponential_sign_cancellation
end Erdos371
