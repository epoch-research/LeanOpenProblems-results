import Submission.CanonicalPairKernel
open Erdos184Work.PairJunctionCoding Erdos184Work.PairSlotMarkers Erdos184Work.CanonicalPairLayout
open Erdos184Work.CanonicalPairKernel Erdos184Work.CycleSegments
namespace CheckCanonicalCompute
def b : PairIndex 4 → Fin 3 := fun _ => 1
lemma hb : ∀ i, 2 ≤ (markers b i).card := by decide +kernel
example : place b hb 0 0 = 2 := by
  rw [place,Finset.orderEmbOfFin_apply]
  decide +kernel
example : ∀ o : Marked.Order 1, (Erdos184Work.SmallOrderNormalization.normalized 1 o).vertex 0 = 0 := by decide +kernel
end CheckCanonicalCompute
