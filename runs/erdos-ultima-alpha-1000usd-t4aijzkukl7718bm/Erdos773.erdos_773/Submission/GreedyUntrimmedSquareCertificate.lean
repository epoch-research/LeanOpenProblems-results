import Submission.GreedyRelaxedExtraction
import Submission.GreedyCodegreeSquareCertificate

/-! Square-Sidon extraction with a supplied uniform degree bound, without trimming. -/
namespace Erdos773.GreedyUntrimmedSquareCertificate
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
open SquareCollisionLinearization HypergraphDegreeTrim GreedyHorizonFactors GreedyCodegreeSquareCertificate
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

/-- The entire supplied carrier is used. No degree-trimming term is lost. -/
theorem eventually_certificate (Aexp : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (m:ℝ)^25 →
      ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → (N:ℝ) ≤ (m:ℝ)^Aexp →
      ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (pairEdges A a b).card ≤ m^3) →
      (∀ a ∈ A, degree (edges A) a ≤ m^300) →
      τ*(A.card:ℝ)/((100/99:ℝ)*(m:ℝ)^100) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  filter_upwards [GreedyRelaxedExtraction.eventually_selection (α := ℕ) Aexp] with m hm
  intro τ hτ hbudget N A hAN hNm hAP hcodeg hdegrees
  have hAupper : (A.card:ℝ) ≤ (m:ℝ)^Aexp := by
    have hh : A.card ≤ N := by simpa using card_le_card hAN
    exact (by exact_mod_cast hh : (A.card:ℝ) ≤ N).trans hNm
  obtain ⟨I,hIB,hI,hIcard⟩ := hm τ hτ hbudget A hAupper (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he f hf hne => intersection_card_le_two hAP he hf hne) hdegrees hcodeg
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIB hAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card ≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIB.trans hAN)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ) ≠ 0))] at hmax
  rw [mul_comm τ]
  exact hIcard.trans (by exact_mod_cast hmax)

#print axioms eventually_certificate
end
end Erdos773.GreedyUntrimmedSquareCertificate
