import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_333_0 : CompleteAt 333 0 := by decide +kernel
lemma complete_333_1 : CompleteAt 333 1 := by decide +kernel
lemma complete_333_2 : CompleteAt 333 2 := by decide +kernel
lemma complete_333_3 : CompleteAt 333 3 := by decide +kernel
lemma complete_333_4 : CompleteAt 333 4 := by decide +kernel
lemma complete_case333 : ∀ e0, CompleteAt 333 e0 := by
  intro e0
  fin_cases e0
  · exact complete_333_0
  · exact complete_333_1
  · exact complete_333_2
  · exact complete_333_3
  · exact complete_333_4
#print axioms complete_case333
end Erdos184Work.PureSixLocalFilter1
