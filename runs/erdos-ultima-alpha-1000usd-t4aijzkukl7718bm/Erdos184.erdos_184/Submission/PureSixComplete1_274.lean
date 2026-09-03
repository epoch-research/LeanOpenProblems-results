import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_274_0 : CompleteAt 274 0 := by decide +kernel
lemma complete_274_1 : CompleteAt 274 1 := by decide +kernel
lemma complete_274_2 : CompleteAt 274 2 := by decide +kernel
lemma complete_274_3 : CompleteAt 274 3 := by decide +kernel
lemma complete_274_4 : CompleteAt 274 4 := by decide +kernel
lemma complete_case274 : ∀ e0, CompleteAt 274 e0 := by
  intro e0
  fin_cases e0
  · exact complete_274_0
  · exact complete_274_1
  · exact complete_274_2
  · exact complete_274_3
  · exact complete_274_4
#print axioms complete_case274
end Erdos184Work.PureSixLocalFilter1
