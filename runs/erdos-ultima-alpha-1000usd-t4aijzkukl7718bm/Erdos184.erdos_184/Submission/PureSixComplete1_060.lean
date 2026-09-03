import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_60_0 : CompleteAt 60 0 := by decide +kernel
lemma complete_60_1 : CompleteAt 60 1 := by decide +kernel
lemma complete_60_2 : CompleteAt 60 2 := by decide +kernel
lemma complete_60_3 : CompleteAt 60 3 := by decide +kernel
lemma complete_60_4 : CompleteAt 60 4 := by decide +kernel
lemma complete_case60 : ∀ e0, CompleteAt 60 e0 := by
  intro e0
  fin_cases e0
  · exact complete_60_0
  · exact complete_60_1
  · exact complete_60_2
  · exact complete_60_3
  · exact complete_60_4
#print axioms complete_case60
end Erdos184Work.PureSixLocalFilter1
