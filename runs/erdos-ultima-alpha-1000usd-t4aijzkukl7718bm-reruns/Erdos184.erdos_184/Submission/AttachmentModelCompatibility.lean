import Submission.AttachmentModelFacts
import Submission.SmallGraphEncoding

/-! Compatibility of the attachment bases with cycle and outside encodings. -/
open SimpleGraph
namespace Erdos184.AttachmentModelCompatibility
open CountThreeAttachmentData AttachmentModelFacts SmallGraphEncoding
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 4096

lemma base_active : ∀ i : Fin 12, ∀ v w : Fin 11, s(v,w) ∈ (model i).base →
    v.val < (model i).girth + (model i).outsideOrder ∧
    w.val < (model i).girth + (model i).outsideOrder := by
  decide +kernel

lemma base_cycle : ∀ i : Fin 12, ∀ u v : Fin (model i).girth,
    (cycleGraph (model i).girth).Adj u v ↔
      s(Fin.ofNat 11 u.val,Fin.ofNat 11 v.val) ∈ (model i).base := by
  decide +kernel

def outsideRootDegree : Fin 12 → ℕ := ![1,2,2,1,2,3,2,2,2,2,2,2]
def outsideCode : Fin 12 → ℕ := ![0,1,7,63,62,504,6,30,504,742,798,15242]

lemma base_outside : ∀ i : Fin 12, ∀ u v : Fin (model i).outsideOrder,
    starAdj (outsideRootDegree i) (outsideCode i) u.val v.val = true ↔
      s(outsideVertex (model i) u.val,outsideVertex (model i) v.val) ∈ (model i).base := by
  decide +kernel

end Erdos184.AttachmentModelCompatibility
