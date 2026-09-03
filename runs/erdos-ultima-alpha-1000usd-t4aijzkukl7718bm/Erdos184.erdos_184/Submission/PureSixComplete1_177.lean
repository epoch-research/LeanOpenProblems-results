import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_177_0 : CompleteAt 177 0 := by decide +kernel
lemma complete_177_1 : CompleteAt 177 1 := by decide +kernel
lemma complete_177_2 : CompleteAt 177 2 := by decide +kernel
lemma complete_177_3 : CompleteAt 177 3 := by decide +kernel
lemma complete_177_4 : CompleteAt 177 4 := by decide +kernel
lemma complete_case177 : ∀ e0, CompleteAt 177 e0 := by
  intro e0
  fin_cases e0
  · exact complete_177_0
  · exact complete_177_1
  · exact complete_177_2
  · exact complete_177_3
  · exact complete_177_4
#print axioms complete_case177
end Erdos184Work.PureSixLocalFilter1
