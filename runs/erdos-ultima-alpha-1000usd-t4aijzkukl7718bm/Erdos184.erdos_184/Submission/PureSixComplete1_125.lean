import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_125_0 : CompleteAt 125 0 := by decide +kernel
lemma complete_125_1 : CompleteAt 125 1 := by decide +kernel
lemma complete_125_2 : CompleteAt 125 2 := by decide +kernel
lemma complete_125_3 : CompleteAt 125 3 := by decide +kernel
lemma complete_125_4 : CompleteAt 125 4 := by decide +kernel
lemma complete_case125 : ∀ e0, CompleteAt 125 e0 := by
  intro e0
  fin_cases e0
  · exact complete_125_0
  · exact complete_125_1
  · exact complete_125_2
  · exact complete_125_3
  · exact complete_125_4
#print axioms complete_case125
end Erdos184Work.PureSixLocalFilter1
