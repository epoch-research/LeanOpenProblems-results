import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_219_0 : CompleteAt 219 0 := by decide +kernel
lemma complete_219_1 : CompleteAt 219 1 := by decide +kernel
lemma complete_219_2 : CompleteAt 219 2 := by decide +kernel
lemma complete_219_3 : CompleteAt 219 3 := by decide +kernel
lemma complete_219_4 : CompleteAt 219 4 := by decide +kernel
lemma complete_case219 : ∀ e0, CompleteAt 219 e0 := by
  intro e0
  fin_cases e0
  · exact complete_219_0
  · exact complete_219_1
  · exact complete_219_2
  · exact complete_219_3
  · exact complete_219_4
#print axioms complete_case219
end Erdos184Work.PureSixLocalFilter1
