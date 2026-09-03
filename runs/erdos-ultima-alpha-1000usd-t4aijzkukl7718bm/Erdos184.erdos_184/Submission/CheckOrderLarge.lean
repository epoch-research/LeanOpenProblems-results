import Submission.OrderNormalizationDefs
/-! Resource check for separate finite normalization cases. -/
open Erdos184Work.CycleSegments Erdos184Work.SmallOrderNormalization
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option Elab.async false
lemma check4 : ∀ o : Marked.Order 4, (normalized 4 o).Valid id (Marked.nextFin 4 o) := by decide
#check check4
lemma check5 : ∀ o : Marked.Order 5, (normalized 5 o).Valid id (Marked.nextFin 5 o) := by
  rintro ⟨⟨⟨p,i⟩,j⟩,k⟩
  fin_cases k <;> fin_cases j <;> fin_cases i <;> revert p <;> decide
#check check5
