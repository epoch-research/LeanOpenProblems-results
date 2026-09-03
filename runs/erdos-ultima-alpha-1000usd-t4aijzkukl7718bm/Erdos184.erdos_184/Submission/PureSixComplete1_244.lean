import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_244_0 : CompleteAt 244 0 := by decide +kernel
lemma complete_244_1 : CompleteAt 244 1 := by decide +kernel
lemma complete_244_2 : CompleteAt 244 2 := by decide +kernel
lemma complete_244_3 : CompleteAt 244 3 := by decide +kernel
lemma complete_244_4 : CompleteAt 244 4 := by decide +kernel
lemma complete_case244 : ∀ e0, CompleteAt 244 e0 := by
  intro e0
  fin_cases e0
  · exact complete_244_0
  · exact complete_244_1
  · exact complete_244_2
  · exact complete_244_3
  · exact complete_244_4
#print axioms complete_case244
end Erdos184Work.PureSixLocalFilter1
