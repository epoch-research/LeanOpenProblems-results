import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_173_0 : CompleteAt 173 0 := by decide +kernel
lemma complete_173_1 : CompleteAt 173 1 := by decide +kernel
lemma complete_173_2 : CompleteAt 173 2 := by decide +kernel
lemma complete_173_3 : CompleteAt 173 3 := by decide +kernel
lemma complete_173_4 : CompleteAt 173 4 := by decide +kernel
lemma complete_case173 : ∀ e0, CompleteAt 173 e0 := by
  intro e0
  fin_cases e0
  · exact complete_173_0
  · exact complete_173_1
  · exact complete_173_2
  · exact complete_173_3
  · exact complete_173_4
#print axioms complete_case173
end Erdos184Work.PureSixLocalFilter1
