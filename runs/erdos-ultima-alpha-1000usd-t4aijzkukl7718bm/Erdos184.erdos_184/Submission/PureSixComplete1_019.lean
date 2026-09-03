import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_19_0 : CompleteAt 19 0 := by decide +kernel
lemma complete_19_1 : CompleteAt 19 1 := by decide +kernel
lemma complete_19_2 : CompleteAt 19 2 := by decide +kernel
lemma complete_19_3 : CompleteAt 19 3 := by decide +kernel
lemma complete_19_4 : CompleteAt 19 4 := by decide +kernel
lemma complete_case19 : ∀ e0, CompleteAt 19 e0 := by
  intro e0
  fin_cases e0
  · exact complete_19_0
  · exact complete_19_1
  · exact complete_19_2
  · exact complete_19_3
  · exact complete_19_4
#print axioms complete_case19
end Erdos184Work.PureSixLocalFilter1
