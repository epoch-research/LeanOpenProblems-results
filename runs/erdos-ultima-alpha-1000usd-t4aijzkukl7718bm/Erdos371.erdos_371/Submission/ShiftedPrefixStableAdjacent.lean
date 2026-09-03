import Submission.ShiftedPrefixEndpointLaw
import Submission.HarmonicPrefixStableAdjacent

/-! The natural adjacent-transfer error is negligible in absolute mean over
moving windows of global prefix endpoints. The endpoint floor(N/p) is retained. -/
namespace Erdos371.FiniteInformation
open Finset Filter
open scoped Topology
set_option autoImplicit false

lemma shiftedPrefixAdjacentTransferError_zero {X : Type*} (p : ℕ) (hp : 0 < p) (L : ℕ → X)
    (hL : Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1) (A M : ℕ → ℕ)
    (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => shiftedHarmonicMean (A j) (M j)
      (fun N => |naturalAdjacentTransferError p N L C|)) atTop (𝓝 0) :=
  shiftedHarmonicMean_abs_zero (fun N => naturalAdjacentTransferError p N L C)
    ((p : ℝ)+1) (by positivity) (fun N => naturalAdjacentTransferError_bound p N L C hC)
    (naturalAdjacentTransferError_zero p hp L hL C hC) A M hH

lemma shiftedPrefixAdjacentTransferError_average_zero {X : Type*} (L : ℕ → X)
    (hL : ∀ p, 0 < p → Tendsto (fun N => prefixMean N (labelDilationDefect p L)) atTop (𝓝 0))
    (P : Finset ℕ) (hP : ∀ p ∈ P, 0 < p) (C : X → X → ℝ) (hC : ∀ a b, |C a b| ≤ 1)
    (A M : ℕ → ℕ) (hH : Tendsto (fun j => shiftedHarmonicMass (A j) (M j)) atTop atTop) :
    Tendsto (fun j => mean (shiftedEndpointLaw (A j) (M j)) (fun i =>
      |(∑ p ∈ P, naturalAdjacentTransferError p (shiftedEndpoint (A j) (M j) i) L C)/(P.card : ℝ)|))
      atTop (𝓝 0) := by
  have ht := (tendsto_finset_sum P (fun p hp =>
    shiftedPrefixAdjacentTransferError_zero p (hP p hp) L (hL p (hP p hp)) C hC A M hH)).div_const (P.card : ℝ)
  simp only [sum_const_zero,zero_div] at ht
  apply squeeze_zero (fun _ => mean_nonneg_of_nonneg _ _ (fun _ => abs_nonneg _)) _ ht
  intro j
  have h := mean_abs_finset_average_le (shiftedEndpointLaw (A j) (M j)) P
    (fun p i => naturalAdjacentTransferError p (shiftedEndpoint (A j) (M j) i) L C)
  have he (p : ℕ) : mean (shiftedEndpointLaw (A j) (M j))
      (fun i => |naturalAdjacentTransferError p (shiftedEndpoint (A j) (M j) i) L C|) =
      shiftedHarmonicMean (A j) (M j) (fun N => |naturalAdjacentTransferError p N L C|) :=
    shiftedEndpointLaw_mean (A j) (M j) (fun N => |naturalAdjacentTransferError p N L C|)
  simpa only [he] using h

#print axioms shiftedPrefixAdjacentTransferError_average_zero
end Erdos371.FiniteInformation
