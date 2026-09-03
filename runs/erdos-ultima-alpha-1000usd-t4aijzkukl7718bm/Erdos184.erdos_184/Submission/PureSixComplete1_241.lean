import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_241_0 : CompleteAt 241 0 := by decide +kernel
lemma complete_241_1 : CompleteAt 241 1 := by decide +kernel
lemma complete_241_2 : CompleteAt 241 2 := by decide +kernel
lemma complete_241_3 : CompleteAt 241 3 := by decide +kernel
lemma complete_241_4 : CompleteAt 241 4 := by decide +kernel
lemma complete_case241 : ∀ e0, CompleteAt 241 e0 := by
  intro e0
  fin_cases e0
  · exact complete_241_0
  · exact complete_241_1
  · exact complete_241_2
  · exact complete_241_3
  · exact complete_241_4
#print axioms complete_case241
end Erdos184Work.PureSixLocalFilter1
