import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_374_0 : CompleteAt 374 0 := by decide +kernel
lemma complete_374_1 : CompleteAt 374 1 := by decide +kernel
lemma complete_374_2 : CompleteAt 374 2 := by decide +kernel
lemma complete_374_3 : CompleteAt 374 3 := by decide +kernel
lemma complete_374_4 : CompleteAt 374 4 := by decide +kernel
lemma complete_case374 : ∀ e0, CompleteAt 374 e0 := by
  intro e0
  fin_cases e0
  · exact complete_374_0
  · exact complete_374_1
  · exact complete_374_2
  · exact complete_374_3
  · exact complete_374_4
#print axioms complete_case374
end Erdos184Work.PureSixLocalFilter1
