import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_267_0 : CompleteAt 267 0 := by decide +kernel
lemma complete_267_1 : CompleteAt 267 1 := by decide +kernel
lemma complete_267_2 : CompleteAt 267 2 := by decide +kernel
lemma complete_267_3 : CompleteAt 267 3 := by decide +kernel
lemma complete_267_4 : CompleteAt 267 4 := by decide +kernel
lemma complete_case267 : ∀ e0, CompleteAt 267 e0 := by
  intro e0
  fin_cases e0
  · exact complete_267_0
  · exact complete_267_1
  · exact complete_267_2
  · exact complete_267_3
  · exact complete_267_4
#print axioms complete_case267
end Erdos184Work.PureSixLocalFilter1
