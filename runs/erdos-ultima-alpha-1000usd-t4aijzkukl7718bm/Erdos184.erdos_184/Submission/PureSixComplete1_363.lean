import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_363_0 : CompleteAt 363 0 := by decide +kernel
lemma complete_363_1 : CompleteAt 363 1 := by decide +kernel
lemma complete_363_2 : CompleteAt 363 2 := by decide +kernel
lemma complete_363_3 : CompleteAt 363 3 := by decide +kernel
lemma complete_363_4 : CompleteAt 363 4 := by decide +kernel
lemma complete_case363 : ∀ e0, CompleteAt 363 e0 := by
  intro e0
  fin_cases e0
  · exact complete_363_0
  · exact complete_363_1
  · exact complete_363_2
  · exact complete_363_3
  · exact complete_363_4
#print axioms complete_case363
end Erdos184Work.PureSixLocalFilter1
