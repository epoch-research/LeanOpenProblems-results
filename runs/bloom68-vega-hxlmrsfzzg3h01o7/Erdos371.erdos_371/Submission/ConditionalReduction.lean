import Submission.DyadicFacts
import Submission.ScaleTauberian

/-!
A conditional reduction, not a proof of Erdős 371. Both the bypass mean
hypothesis and access hypothesis remain explicit theorem assumptions.
The original specification is neither imported nor used.
-/

namespace Erdos371Dyadic

open Filter
open Erdos371Scale

/-- Exact sufficient conditions. In particular, no unsupported implication
from logarithmic density to ordinary density is used. -/
theorem hasDensity_of_bypassMean_zero_of_access
    (hT : Tendsto (fun N : ℕ => (T N : ℝ) / (N : ℝ)) atTop (nhds 0))
    (haccess : BoundedDyadicAccess (fun N : ℕ => (D N : ℝ) / (N : ℝ))) :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) := by
  apply hasDensity_iff_signedMean.mpr
  apply tendsto_zero_of_flatness_of_access _ haccess
  simpa only [Nat.cast_mul, Nat.cast_ofNat] using
    dyadic_flatness_iff_bypassMean_zero.mpr hT

/-- An equivalence with explicit, still-unproved hypotheses, not a closed
proof of the density statement. -/
theorem hasDensity_iff_bypassMean_zero_and_access :
    {n | Nat.maxPrimeFac (n + 1) > Nat.maxPrimeFac n}.HasDensity (1 / 2) ↔
      Tendsto (fun N : ℕ => (T N : ℝ) / (N : ℝ)) atTop (nhds 0) ∧
      BoundedDyadicAccess (fun N : ℕ => (D N : ℝ) / (N : ℝ)) := by
  constructor
  · intro h
    have hD := hasDensity_iff_signedMean.mp h
    have hT := bypassMean_zero_of_hasDensity h
    refine ⟨hT, ?_⟩
    apply (access_iff_tendsto_zero ?_).mpr hD
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      dyadic_flatness_iff_bypassMean_zero.mpr hT
  · rintro ⟨hT, ha⟩
    exact hasDensity_of_bypassMean_zero_of_access hT ha

#print axioms hasDensity_of_bypassMean_zero_of_access
#print axioms hasDensity_iff_bypassMean_zero_and_access

end Erdos371Dyadic
