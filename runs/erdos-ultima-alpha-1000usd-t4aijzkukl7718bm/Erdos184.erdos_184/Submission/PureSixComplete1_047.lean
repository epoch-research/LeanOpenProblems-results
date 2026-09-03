import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_47_0 : CompleteAt 47 0 := by decide +kernel
lemma complete_47_1 : CompleteAt 47 1 := by decide +kernel
lemma complete_47_2 : CompleteAt 47 2 := by decide +kernel
lemma complete_47_3 : CompleteAt 47 3 := by decide +kernel
lemma complete_47_4 : CompleteAt 47 4 := by decide +kernel
lemma complete_case47 : ∀ e0, CompleteAt 47 e0 := by
  intro e0
  fin_cases e0
  · exact complete_47_0
  · exact complete_47_1
  · exact complete_47_2
  · exact complete_47_3
  · exact complete_47_4
#print axioms complete_case47
end Erdos184Work.PureSixLocalFilter1
