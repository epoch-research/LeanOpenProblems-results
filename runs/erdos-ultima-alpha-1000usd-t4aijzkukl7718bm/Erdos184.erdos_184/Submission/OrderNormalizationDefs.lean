import Submission.FastMarkedOrder
import Submission.LabelCycleCertificates

/-! Finite normalization of the cyclic-order encodings needed for small
contact kernels. The verified range is two through seven markers. -/
namespace Erdos184Work.SmallOrderNormalization
open CycleSegments LabelKernel
set_option maxHeartbeats 0
set_option maxRecDepth 100000

def raw (n : ℕ) (o : Marked.Order n) (i : Fin (n+2)) : Fin (n+2) :=
  (Marked.fastNext n o)^[i.val] 0

def forward (n : ℕ) (o : Marked.Order n) : Bool :=
  decide ((raw n o 1).val < (raw n o (Fin.last (n+1))).val)

def normalized (n : ℕ) (o : Marked.Order n) : CycleData (Fin (n+2)) (Fin (n+2)) where
  size := n
  edge i := if forward n o then raw n o i else raw n o (-i-1)
  vertex i := if forward n o then raw n o i else raw n o (-i)


end Erdos184Work.SmallOrderNormalization
