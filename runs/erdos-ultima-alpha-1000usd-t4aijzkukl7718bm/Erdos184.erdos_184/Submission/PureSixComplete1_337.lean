import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_337_0 : CompleteAt 337 0 := by decide +kernel
lemma complete_337_1 : CompleteAt 337 1 := by decide +kernel
lemma complete_337_2 : CompleteAt 337 2 := by decide +kernel
lemma complete_337_3 : CompleteAt 337 3 := by decide +kernel
lemma complete_337_4 : CompleteAt 337 4 := by decide +kernel
lemma complete_case337 : ∀ e0, CompleteAt 337 e0 := by
  intro e0
  fin_cases e0
  · exact complete_337_0
  · exact complete_337_1
  · exact complete_337_2
  · exact complete_337_3
  · exact complete_337_4
#print axioms complete_case337
end Erdos184Work.PureSixLocalFilter1
