import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_98_0 : CompleteAt 98 0 := by decide +kernel
lemma complete_98_1 : CompleteAt 98 1 := by decide +kernel
lemma complete_98_2 : CompleteAt 98 2 := by decide +kernel
lemma complete_98_3 : CompleteAt 98 3 := by decide +kernel
lemma complete_98_4 : CompleteAt 98 4 := by decide +kernel
lemma complete_case98 : ∀ e0, CompleteAt 98 e0 := by
  intro e0
  fin_cases e0
  · exact complete_98_0
  · exact complete_98_1
  · exact complete_98_2
  · exact complete_98_3
  · exact complete_98_4
#print axioms complete_case98
end Erdos184Work.PureSixLocalFilter1
