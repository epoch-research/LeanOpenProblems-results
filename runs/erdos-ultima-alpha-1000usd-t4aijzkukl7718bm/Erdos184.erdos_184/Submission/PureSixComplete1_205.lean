import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_205_0 : CompleteAt 205 0 := by decide +kernel
lemma complete_205_1 : CompleteAt 205 1 := by decide +kernel
lemma complete_205_2 : CompleteAt 205 2 := by decide +kernel
lemma complete_205_3 : CompleteAt 205 3 := by decide +kernel
lemma complete_205_4 : CompleteAt 205 4 := by decide +kernel
lemma complete_case205 : ∀ e0, CompleteAt 205 e0 := by
  intro e0
  fin_cases e0
  · exact complete_205_0
  · exact complete_205_1
  · exact complete_205_2
  · exact complete_205_3
  · exact complete_205_4
#print axioms complete_case205
end Erdos184Work.PureSixLocalFilter1
