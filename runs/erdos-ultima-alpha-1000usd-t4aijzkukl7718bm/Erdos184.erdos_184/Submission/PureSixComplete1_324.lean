import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_324_0 : CompleteAt 324 0 := by decide +kernel
lemma complete_324_1 : CompleteAt 324 1 := by decide +kernel
lemma complete_324_2 : CompleteAt 324 2 := by decide +kernel
lemma complete_324_3 : CompleteAt 324 3 := by decide +kernel
lemma complete_324_4 : CompleteAt 324 4 := by decide +kernel
lemma complete_case324 : ∀ e0, CompleteAt 324 e0 := by
  intro e0
  fin_cases e0
  · exact complete_324_0
  · exact complete_324_1
  · exact complete_324_2
  · exact complete_324_3
  · exact complete_324_4
#print axioms complete_case324
end Erdos184Work.PureSixLocalFilter1
