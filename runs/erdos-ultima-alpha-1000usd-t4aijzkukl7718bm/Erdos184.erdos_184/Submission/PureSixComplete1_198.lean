import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_198_0 : CompleteAt 198 0 := by decide +kernel
lemma complete_198_1 : CompleteAt 198 1 := by decide +kernel
lemma complete_198_2 : CompleteAt 198 2 := by decide +kernel
lemma complete_198_3 : CompleteAt 198 3 := by decide +kernel
lemma complete_198_4 : CompleteAt 198 4 := by decide +kernel
lemma complete_case198 : ∀ e0, CompleteAt 198 e0 := by
  intro e0
  fin_cases e0
  · exact complete_198_0
  · exact complete_198_1
  · exact complete_198_2
  · exact complete_198_3
  · exact complete_198_4
#print axioms complete_case198
end Erdos184Work.PureSixLocalFilter1
