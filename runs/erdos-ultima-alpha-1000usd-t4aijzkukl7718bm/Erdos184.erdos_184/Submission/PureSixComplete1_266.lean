import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_266_0 : CompleteAt 266 0 := by decide +kernel
lemma complete_266_1 : CompleteAt 266 1 := by decide +kernel
lemma complete_266_2 : CompleteAt 266 2 := by decide +kernel
lemma complete_266_3 : CompleteAt 266 3 := by decide +kernel
lemma complete_266_4 : CompleteAt 266 4 := by decide +kernel
lemma complete_case266 : ∀ e0, CompleteAt 266 e0 := by
  intro e0
  fin_cases e0
  · exact complete_266_0
  · exact complete_266_1
  · exact complete_266_2
  · exact complete_266_3
  · exact complete_266_4
#print axioms complete_case266
end Erdos184Work.PureSixLocalFilter1
