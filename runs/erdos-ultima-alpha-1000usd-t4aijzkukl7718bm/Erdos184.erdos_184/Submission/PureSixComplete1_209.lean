import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_209_0 : CompleteAt 209 0 := by decide +kernel
lemma complete_209_1 : CompleteAt 209 1 := by decide +kernel
lemma complete_209_2 : CompleteAt 209 2 := by decide +kernel
lemma complete_209_3 : CompleteAt 209 3 := by decide +kernel
lemma complete_209_4 : CompleteAt 209 4 := by decide +kernel
lemma complete_case209 : ∀ e0, CompleteAt 209 e0 := by
  intro e0
  fin_cases e0
  · exact complete_209_0
  · exact complete_209_1
  · exact complete_209_2
  · exact complete_209_3
  · exact complete_209_4
#print axioms complete_case209
end Erdos184Work.PureSixLocalFilter1
