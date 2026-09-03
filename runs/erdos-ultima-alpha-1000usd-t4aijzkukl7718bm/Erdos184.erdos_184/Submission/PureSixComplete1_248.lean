import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_248_0 : CompleteAt 248 0 := by decide +kernel
lemma complete_248_1 : CompleteAt 248 1 := by decide +kernel
lemma complete_248_2 : CompleteAt 248 2 := by decide +kernel
lemma complete_248_3 : CompleteAt 248 3 := by decide +kernel
lemma complete_248_4 : CompleteAt 248 4 := by decide +kernel
lemma complete_case248 : ∀ e0, CompleteAt 248 e0 := by
  intro e0
  fin_cases e0
  · exact complete_248_0
  · exact complete_248_1
  · exact complete_248_2
  · exact complete_248_3
  · exact complete_248_4
#print axioms complete_case248
end Erdos184Work.PureSixLocalFilter1
