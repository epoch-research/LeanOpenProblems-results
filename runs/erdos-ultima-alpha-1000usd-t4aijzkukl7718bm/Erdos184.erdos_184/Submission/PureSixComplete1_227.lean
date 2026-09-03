import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_227_0 : CompleteAt 227 0 := by decide +kernel
lemma complete_227_1 : CompleteAt 227 1 := by decide +kernel
lemma complete_227_2 : CompleteAt 227 2 := by decide +kernel
lemma complete_227_3 : CompleteAt 227 3 := by decide +kernel
lemma complete_227_4 : CompleteAt 227 4 := by decide +kernel
lemma complete_case227 : ∀ e0, CompleteAt 227 e0 := by
  intro e0
  fin_cases e0
  · exact complete_227_0
  · exact complete_227_1
  · exact complete_227_2
  · exact complete_227_3
  · exact complete_227_4
#print axioms complete_case227
end Erdos184Work.PureSixLocalFilter1
