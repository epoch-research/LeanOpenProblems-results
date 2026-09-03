import Submission.GreedyBatchInitialExtraction
import Submission.PrioritySquareSidonLower
import Submission.SquareCollisionIntersections

/-! A finite square-Sidon certificate using the shrinking mixed profiles. -/
namespace Erdos773.GreedyBatchSquareCertificate
open Finset SquareCollisionCodegrees SquareCollisionIntersections HypergraphDegreeTrim
open GreedyBatchDensityProfile GreedyBatchProfileStep GreedyBatchVolume
set_option maxHeartbeats 3000000
noncomputable section

theorem certificate (N m K : ℕ) (d T : ℝ) (P : ℕ) (A : Finset ℕ)
    (hm : 2000000≤ m) (hmV : 3*increment (K+increment K)≤ m)
    (hd : 0<d) (hdU : d≤(m:ℝ)^K) (hP : 1≤P) (hPm : P≤ m)
    (hT : 1≤T) (hT3 : T^3≤(m:ℝ)/16)
    (hterminal : (m:ℝ)^1000≤d*Real.exp (-a m*((T+1)^3-1)))
    (hA : A⊆Icc 1 N) (hvol : N≤ m^K)
    (hAP : ThreeAPFree ((A.image (fun n : ℕ => n^2)):Set ℕ))
    (hdegree : ∀ x ∈ A, (degree (edges A) x:ℝ)≤d^3)
    (hpair : ∀ x ∈ A, ∀ y ∈ A, x≠y → (pairEdges A x y).card≤P) :
    efficiency m*(T-1)/d*A.card≤
      (maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)):ℝ) := by
  classical
  have hAc : A.card≤N := by simpa using card_le_card hA
  obtain ⟨I,hIA,hI,hcard⟩ := GreedyBatchInitialExtraction.selection A (edges A) m K d T P
    hm hmV hd hdU hP hPm hT hT3 hterminal (hAc.trans hvol)
    (fun e he => mem_powerset.mp (mem_filter.mp he).1)
    (fun e he => (mem_filter.mp he).2.1) hdegree hpair
    (fun e he f hf hne => intersection_card_le_two hAP he hf hne)
  have hsidon := PrioritySquareSidonLower.sidon_of_edge_avoidance hIA hAP hI
  have hmax : (I.image (fun n : ℕ => n^2)).card≤
      maxSidonSubsetCard ((Icc 1 N).image (fun n : ℕ => n^2)) :=
    le_sup (mem_filter.mpr ⟨mem_powerset.mpr (image_subset_image (hIA.trans hA)),hsidon⟩)
  rw [card_image_of_injective I (Nat.pow_left_injective (by omega : (2:ℕ)≠0))] at hmax
  exact hcard.trans (by exact_mod_cast hmax)

#print axioms certificate
end
end Erdos773.GreedyBatchSquareCertificate
