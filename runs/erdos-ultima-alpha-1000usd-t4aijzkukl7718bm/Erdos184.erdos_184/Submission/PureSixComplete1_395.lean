import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_395_0 : CompleteAt 395 0 := by decide +kernel
lemma complete_395_1 : CompleteAt 395 1 := by decide +kernel
lemma complete_395_2 : CompleteAt 395 2 := by decide +kernel
lemma complete_395_3 : CompleteAt 395 3 := by decide +kernel
lemma complete_395_4 : CompleteAt 395 4 := by decide +kernel
lemma complete_case395 : ∀ e0, CompleteAt 395 e0 := by
  intro e0
  fin_cases e0
  · exact complete_395_0
  · exact complete_395_1
  · exact complete_395_2
  · exact complete_395_3
  · exact complete_395_4
#print axioms complete_case395
end Erdos184Work.PureSixLocalFilter1
