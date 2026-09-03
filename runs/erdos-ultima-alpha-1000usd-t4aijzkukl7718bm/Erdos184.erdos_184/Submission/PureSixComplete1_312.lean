import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_312_0 : CompleteAt 312 0 := by decide +kernel
lemma complete_312_1 : CompleteAt 312 1 := by decide +kernel
lemma complete_312_2 : CompleteAt 312 2 := by decide +kernel
lemma complete_312_3 : CompleteAt 312 3 := by decide +kernel
lemma complete_312_4 : CompleteAt 312 4 := by decide +kernel
lemma complete_case312 : ∀ e0, CompleteAt 312 e0 := by
  intro e0
  fin_cases e0
  · exact complete_312_0
  · exact complete_312_1
  · exact complete_312_2
  · exact complete_312_3
  · exact complete_312_4
#print axioms complete_case312
end Erdos184Work.PureSixLocalFilter1
