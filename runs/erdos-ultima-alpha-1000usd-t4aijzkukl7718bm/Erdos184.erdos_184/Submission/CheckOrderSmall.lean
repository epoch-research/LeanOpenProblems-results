import Submission.OrderNormalizationDefs
open Erdos184Work.CycleSegments Erdos184Work.SmallOrderNormalization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
lemma check0 : ∀ o : Marked.Order 0, (normalized 0 o).Valid id (Marked.nextFin 0 o) := by decide
#check check0
lemma check1 : ∀ o : Marked.Order 1, (normalized 1 o).Valid id (Marked.nextFin 1 o) := by decide
#check check1
lemma check2 : ∀ o : Marked.Order 2, (normalized 2 o).Valid id (Marked.nextFin 2 o) := by decide
#check check2
lemma check3 : ∀ o : Marked.Order 3, (normalized 3 o).Valid id (Marked.nextFin 3 o) := by decide
#check check3
