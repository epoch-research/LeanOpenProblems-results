import Submission.GreedyGrowingExtraction
import Submission.GreedySquareCertificate

/-!
Square-Sidon extraction with a genuinely growing normalized horizon.
The finite thinning and degree-trimming estimates are reused unchanged.
-/
namespace Erdos773.GreedyGrowingSquareCertificate
open Finset Filter SquareCollisionCodegrees SquareCollisionIntersections
open SquareCollisionLinearization ControlledSquareLinearization ControlledSquareDegrees
open HypergraphDegreeTrim GreedySquareCertificate GreedyHorizonFactors
set_option maxHeartbeats 2500000
noncomputable section

theorem eventually_certificate (Aexp : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ τ : ℝ, 1 ≤ τ → horizonBudget τ ≤ (m:ℝ) → ∀ (N : ℕ) (A : Finset ℕ), A ⊆ Icc 1 N → (N:ℝ) ≤ (m:ℝ)^Aexp →
      ThreeAPFree ((A.image (fun n : ℕ => n^2)) : Set ℕ) →
      ∀ K : ℝ, (∀ a ∈ A, ∀ b ∈ A, a ≠ b → ((pairEdges A a b).card:ℝ) ≤ K) →
      ∀ p μ : ℝ, 0 ≤ p → p ≤ 1 → 0 < μ → 8/μ ≤ (m:ℝ)^24 →
      p^6*(A.card:ℝ)^2*K^2 ≤ p*A.card/4 → μ*p^4*(edges A).card ≤ p*A.card/4 →
      τ*p*A.card/(8*(m:ℝ)^8) ≤
        (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  filter_upwards [GreedyGrowingExtraction.eventually_selection (α := ℕ) Aexp] with m hm
  intro τ hτ hbudget N A hAN hNm hAP K hK p μ hp hp1 hμ hdegree hoverlap hedges
  have hτ0 : 0 ≤ τ := by linarith only [hτ]
  obtain ⟨B,hBA,hBAP,hlin,hBcard,hBdegree⟩ := trimmed_linearization hAP K hK p μ hp hp1 hμ hoverlap hedges
  have hBN : B ⊆ Icc 1 N := hBA.trans hAN
  have hBupper : (B.card:ℝ) ≤ (m:ℝ)^Aexp := by
    have hh : B.card ≤ N := by simpa using card_le_card hBN
    exact (by exact_mod_cast hh : (B.card:ℝ) ≤ N).trans hNm
  have hdegrees : ∀ a ∈ B, degree (edges B) a ≤ m^24 := by
    intro a ha
    exact_mod_cast (hBdegree a ha).trans hdegree
  obtain ⟨I,hIB,hI,hIcard⟩ := hm τ hτ hbudget B hBupper (edges B)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) hlin hdegrees
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIB hBAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card ≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIB.trans hBN)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ) ≠ 0))] at hmax
  have hscale := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hBcard hτ0)
    (by positivity : (0:ℝ) ≤ 2*(m:ℝ)^8)
  have hscale' : τ*p*A.card/(8*(m:ℝ)^8) ≤ B.card*τ/(2*(m:ℝ)^8) := by
    convert hscale using 1; ring
  exact hscale'.trans (hIcard.trans (by exact_mod_cast hmax))

#print axioms eventually_certificate
end
end Erdos773.GreedyGrowingSquareCertificate
