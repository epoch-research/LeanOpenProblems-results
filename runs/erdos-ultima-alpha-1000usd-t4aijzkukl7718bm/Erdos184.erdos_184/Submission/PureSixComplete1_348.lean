import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_348_0 : CompleteAt 348 0 := by decide +kernel
lemma complete_348_1 : CompleteAt 348 1 := by decide +kernel
lemma complete_348_2 : CompleteAt 348 2 := by decide +kernel
lemma complete_348_3 : CompleteAt 348 3 := by decide +kernel
lemma complete_348_4 : CompleteAt 348 4 := by decide +kernel
lemma complete_case348 : ∀ e0, CompleteAt 348 e0 := by
  intro e0
  fin_cases e0
  · exact complete_348_0
  · exact complete_348_1
  · exact complete_348_2
  · exact complete_348_3
  · exact complete_348_4
#print axioms complete_case348
end Erdos184Work.PureSixLocalFilter1
