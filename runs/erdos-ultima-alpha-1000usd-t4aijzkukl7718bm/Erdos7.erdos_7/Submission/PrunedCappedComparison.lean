import Submission.RootPruning
import Submission.CappedHingeLaw

/-! Assembly of filling, a real-count cap, and positive upper trimming.
No arithmetic covering obstruction is claimed here. -/
namespace Erdos7PrunedCappedComparison
open scoped BigOperators
open Erdos7RootPruning
set_option autoImplicit false
set_option maxHeartbeats 2000000

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- Fill discarded points at a lower baseline before capping the comparison
law. Then trim the resulting positive law to the exact retained mass. -/
theorem comparison (μ : Ω → ℝ) (hμ : ∀ x, 0 ≤ μ x) (G : Ω → Prop)
    (X : Ω → ℝ) (b : ℝ) (hb0 : 0 ≤ b) (hbX : ∀ x, b ≤ X x)
    (ν : Ξ → ℝ) (hν : ∀ z, 0 ≤ ν z) (Y : Ξ → ℕ) (k : ℕ)
    (hbk : b ≤ (k+1:ℕ)) (hcap : ∀ x, G x → X x ≤ (k+1:ℕ))
    (hmass : (∑ x, μ x) = ∑ z, ν z)
    (he : Erdos7CappedHingeLaw.excess ν Y k ≤ Erdos7CappedHingeLaw.tailMass ν Y k)
    (hraw : ∀ φ : ℝ → ℝ, ConvexOn ℝ Set.univ φ → Monotone φ →
      (∑ x, μ x*φ (X x)) ≤ ∑ z, ν z*φ (Y z))
    (t : ℝ)
    (φ : ℝ → ℝ) (hφ : ConvexOn ℝ Set.univ φ) (hmφ : Monotone φ) :
    (∑ x, keep μ G x*φ (X x)) ≤
      ∑ z, upperWeight (Erdos7CappedHingeLaw.weight ν Y k)
          (fun z => (Erdos7CappedHingeLaw.value Y k z : ℝ)) t (∑ x, keep μ G x) z *
        φ (upperValue (fun z => (Erdos7CappedHingeLaw.value Y k z : ℝ)) t z) := by
  let F : Ω → ℝ := fill G X b
  have hF (x : Ω) : F x ∈ Set.Icc (0:ℝ) ((k+1:ℕ):ℝ) :=
    ⟨hb0.trans (fill_lower G X b hbX x), fill_upper G X b _ hbk hcap x⟩
  have hfilled (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (hmψ : Monotone ψ) :
      (∑ x, μ x*ψ (F x)) ≤ ∑ z, ν z*ψ (Y z) :=
    (fill_test_le μ hμ G X b hbX ψ hmψ).trans (hraw ψ hψ hmψ)
  have hmean : (∑ x, μ x*F x) ≤ ∑ z, ν z*(Y z:ℝ) := by
    have hc : ConvexOn ℝ Set.univ (fun z : ℝ => z) := by
      simpa using Erdos7FiniteHingeFunctions.convex_affine 1 0
    exact hfilled (fun z => z) hc monotone_id
  have hh (j : ℕ) (_hj : j ≤ k) : (∑ x, μ x*max 0 (F x-j)) ≤
      ∑ z, ν z*max 0 ((Y z:ℝ)-j) :=
    hfilled _ (Erdos7FiniteHingeFunctions.convex_hinge j)
      (Erdos7FiniteHingeFunctions.monotone_hinge j)
  have hcapped (ψ : ℝ → ℝ) (hψ : ConvexOn ℝ Set.univ ψ) (hmψ : Monotone ψ) :
      (∑ x, μ x*ψ (F x)) ≤
        ∑ z, Erdos7CappedHingeLaw.weight ν Y k z * ψ (Erdos7CappedHingeLaw.value Y k z) :=
    Erdos7CappedHingeLaw.capped_comparison μ hμ F ν hν Y k he hF hmass hmean hh ψ hψ hmψ
  apply upperWeight_dominates (keep μ G) (keep_nonneg μ hμ G) X
    (Erdos7CappedHingeLaw.weight ν Y k) (fun z => (Erdos7CappedHingeLaw.value Y k z:ℝ))
    (∑ x, keep μ G x) t rfl _ φ hφ hmφ
  intro ψ hψ hmψ hψ0
  rw [← keep_fill_test μ G X b ψ]
  exact (keep_nonnegative_test_le μ hμ G F ψ hψ0).trans (hcapped ψ hψ hmψ)

/-- The law in `comparison` is nonnegative and has precisely the actual
surviving mass whenever the chosen cutoff tail fits that mass. -/
theorem positive_law (μ : Ω → ℝ) (G : Ω → Prop)
    (ν : Ξ → ℝ) (hν : ∀ z, 0 ≤ ν z) (Y : Ξ → ℕ) (k : ℕ)
    (he : Erdos7CappedHingeLaw.excess ν Y k ≤ Erdos7CappedHingeLaw.tailMass ν Y k)
    (t : ℝ)
    (ht : Erdos7RootPruning.tailMass (Erdos7CappedHingeLaw.weight ν Y k)
      (fun z => (Erdos7CappedHingeLaw.value Y k z:ℝ)) t ≤ ∑ x, keep μ G x) :
    let W := upperWeight (Erdos7CappedHingeLaw.weight ν Y k)
      (fun z => (Erdos7CappedHingeLaw.value Y k z:ℝ)) t (∑ x, keep μ G x)
    (∀ z, 0 ≤ W z) ∧ (∑ z, W z) = ∑ x, keep μ G x := by
  exact ⟨upperWeight_nonneg _ (Erdos7CappedHingeLaw.weight_nonneg ν hν Y k he) _ _ _ ht,
    upperWeight_mass _ _ _ _⟩

#print axioms comparison
#print axioms positive_law
end Erdos7PrunedCappedComparison
