import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_74_0 : CompleteAt 74 0 := by decide +kernel
lemma complete_74_1 : CompleteAt 74 1 := by decide +kernel
lemma complete_74_2 : CompleteAt 74 2 := by decide +kernel
lemma complete_74_3 : CompleteAt 74 3 := by decide +kernel
lemma complete_74_4 : CompleteAt 74 4 := by decide +kernel
lemma complete_case74 : ∀ e0, CompleteAt 74 e0 := by
  intro e0
  fin_cases e0
  · exact complete_74_0
  · exact complete_74_1
  · exact complete_74_2
  · exact complete_74_3
  · exact complete_74_4
#print axioms complete_case74
end Erdos184Work.PureSixLocalFilter1
