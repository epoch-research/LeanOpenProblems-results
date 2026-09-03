import Submission.DoubleSquareOne

namespace Erdos184Work.FourDoubleSquareKernel
open PairJunctionCoding PairSlotMarkers CanonicalPairLayout CycleSegments
open LabelKernel Erdos184Serial
set_option maxHeartbeats 5000000
set_option maxRecDepth 20000
set_option Elab.async false

def rowPlace : Fin 4 → Fin 4 → W :=
  ![![4,5,6,7],![12,13,14,15],![4,5,12,13],![6,7,14,15]]

def rowWord (k : ℕ) : Fin 4 → Fin 4 :=
  if k = 0 then ![0,1,2,3] else if k = 1 then ![0,1,3,2] else ![0,2,1,3]

def localKey (i : Fin 4) (q : Marked.Order (arity counts i)) : ℕ :=
  let v := (SmallOrderNormalization.normalized (arity counts i) q).vertex
  if (v 1).val = 2 then 2 else if (v 2).val = 2 then 0 else 1

def localWord (i : Fin 4) (q : Marked.Order (arity counts i))
    (j : Fin (arity counts i+2)) : W :=
  fastPlace counts marker_bound i ((SmallOrderNormalization.normalized (arity counts i) q).vertex j)

lemma local_word : ∀ (i : Fin 4) (q : Marked.Order (arity counts i))
    (j : Fin (arity counts i+2)), localWord i q j =
    rowPlace i (rowWord (localKey i q) ⟨j.val,by have h := j.isLt; have ha := arity_two i; omega⟩) := by
  decide +kernel

#print axioms local_word
end Erdos184Work.FourDoubleSquareKernel
