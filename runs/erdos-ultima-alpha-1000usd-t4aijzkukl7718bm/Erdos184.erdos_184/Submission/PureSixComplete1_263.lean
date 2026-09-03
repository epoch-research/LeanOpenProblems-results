import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_263_0 : CompleteAt 263 0 := by decide +kernel
lemma complete_263_1 : CompleteAt 263 1 := by decide +kernel
lemma complete_263_2 : CompleteAt 263 2 := by decide +kernel
lemma complete_263_3 : CompleteAt 263 3 := by decide +kernel
lemma complete_263_4 : CompleteAt 263 4 := by decide +kernel
lemma complete_case263 : ∀ e0, CompleteAt 263 e0 := by
  intro e0
  fin_cases e0
  · exact complete_263_0
  · exact complete_263_1
  · exact complete_263_2
  · exact complete_263_3
  · exact complete_263_4
#print axioms complete_case263
end Erdos184Work.PureSixLocalFilter1
