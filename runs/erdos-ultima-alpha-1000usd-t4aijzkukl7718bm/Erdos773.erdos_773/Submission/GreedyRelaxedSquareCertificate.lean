import Submission.GreedyRelaxedExtraction
import Submission.GreedyCodegreeSquareCertificate

/-! Square-Sidon extraction without a linearizing thinning step. -/
namespace Erdos773.GreedyRelaxedSquareCertificate
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
open SquareCollisionLinearization HypergraphDegreeTrim GreedyHorizonFactors GreedyCodegreeSquareCertificate
set_option maxHeartbeats 2500000
set_option maxRecDepth 4096
set_option exponentiation.threshold 1024
noncomputable section

/-- The square collision carrier is retained except for degree trimming.
    The original pair codegrees may be as large as m^3. -/
theorem eventually_certificate (Aexp : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (m:ℝ)^25 →
      ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → (N:ℝ) ≤ (m:ℝ)^Aexp →
      ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ) →
      (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (pairEdges A a b).card ≤ m^3) →
      ∀ D : ℝ, 0 < D → D ≤ (m:ℝ)^300 →
      τ*((A.card:ℝ)-4*(edges A).card/D)/((100/99:ℝ)*(m:ℝ)^100) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  filter_upwards [GreedyRelaxedExtraction.eventually_selection (α := ℕ) Aexp] with m hm
  intro τ hτ hbudget N A hAN hNm hAP hcodeg D hD hDm
  obtain ⟨B,hBA,hBcard,hBdegree⟩ := trim_at_threshold A (edges A)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) D hD
  have hBAP := hAP.mono (show (B.image (fun n : ℕ => n^2):Set ℕ) ⊆ A.image (fun n : ℕ => n^2) by
    exact_mod_cast image_subset_image hBA)
  have hBN := hBA.trans hAN
  have hBupper : (B.card:ℝ) ≤ (m:ℝ)^Aexp := by
    have hh : B.card ≤ N := by simpa using card_le_card hBN
    exact (by exact_mod_cast hh : (B.card:ℝ) ≤ N).trans hNm
  have hdegrees : ∀ a ∈ B, degree (edges B) a ≤ m^300 := by
    intro a ha
    have hmono : (degree (edges B) a:ℝ) ≤ degree (edges A) a := by
      exact_mod_cast degree_mono (edges_mono hBA) a
    exact_mod_cast (hmono.trans (hBdegree a ha)).trans hDm
  have hpairs : ∀ a ∈ B, ∀ b ∈ B, a ≠ b → FourUniformRegularization.pairDegree (edges B) a b ≤ m^3 := by
    intro a ha b hb hab
    exact (card_le_card (pairEdges_mono hBA a b)).trans (hcodeg a (hBA ha) b (hBA hb) hab)
  obtain ⟨I,hIB,hI,hIcard⟩ := hm τ hτ hbudget B hBupper (edges B)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1)
    (fun e he f hf hne => intersection_card_le_two hBAP he hf hne) hdegrees hpairs
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIB hBAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card ≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIB.trans hBN)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ) ≠ 0))] at hmax
  have hscale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hBcard (by linarith only [hτ] : 0 ≤ τ))
    (by positivity : (0:ℝ) ≤ (100/99:ℝ)*(m:ℝ)^100)
  exact hscale.trans (by rw [mul_comm τ]; exact hIcard.trans (by exact_mod_cast hmax))

#print axioms eventually_certificate
end
end Erdos773.GreedyRelaxedSquareCertificate
