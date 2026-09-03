import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_228_0 : CompleteAt 228 0 := by decide +kernel
lemma complete_228_1 : CompleteAt 228 1 := by decide +kernel
lemma complete_228_2 : CompleteAt 228 2 := by decide +kernel
lemma complete_228_3 : CompleteAt 228 3 := by decide +kernel
lemma complete_228_4 : CompleteAt 228 4 := by decide +kernel
lemma complete_case228 : ∀ e0, CompleteAt 228 e0 := by
  intro e0
  fin_cases e0
  · exact complete_228_0
  · exact complete_228_1
  · exact complete_228_2
  · exact complete_228_3
  · exact complete_228_4
#print axioms complete_case228
end Erdos184Work.PureSixLocalFilter1
