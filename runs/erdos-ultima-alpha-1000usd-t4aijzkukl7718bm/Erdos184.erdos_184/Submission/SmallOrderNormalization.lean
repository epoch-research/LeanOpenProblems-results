import Submission.OrderNormalizationTheory

/-! Small-order corollaries of the general structural normalization theorem.
There is no exhaustive computation in these proofs. -/
namespace Erdos184Work.SmallOrderNormalization
open CycleSegments LabelKernel

lemma normalized_valid (n : Fin 6) (o : Marked.Order n.val) :
    (normalized n.val o).Valid id (Marked.nextFin n.val o) :=
  normalized_valid_all n.val o

lemma normalized_first (n : Fin 6) (o : Marked.Order n.val) :
    (normalized n.val o).vertex 0 = 0 := normalized_first_all n.val o

lemma normalized_orientation (n : Fin 6) (o : Marked.Order n.val) :
    n.val = 0 ∨ (normalized n.val o).vertex 1 <
      (normalized n.val o).vertex (Fin.last (n.val+1)) :=
  normalized_orientation_all n.val o

#print axioms normalized_valid
#print axioms normalized_orientation
end Erdos184Work.SmallOrderNormalization
