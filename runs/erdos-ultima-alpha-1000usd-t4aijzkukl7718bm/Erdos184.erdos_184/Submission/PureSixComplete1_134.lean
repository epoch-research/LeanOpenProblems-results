import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_134_0 : CompleteAt 134 0 := by decide +kernel
lemma complete_134_1 : CompleteAt 134 1 := by decide +kernel
lemma complete_134_2 : CompleteAt 134 2 := by decide +kernel
lemma complete_134_3 : CompleteAt 134 3 := by decide +kernel
lemma complete_134_4 : CompleteAt 134 4 := by decide +kernel
lemma complete_case134 : ∀ e0, CompleteAt 134 e0 := by
  intro e0
  fin_cases e0
  · exact complete_134_0
  · exact complete_134_1
  · exact complete_134_2
  · exact complete_134_3
  · exact complete_134_4
#print axioms complete_case134
end Erdos184Work.PureSixLocalFilter1
