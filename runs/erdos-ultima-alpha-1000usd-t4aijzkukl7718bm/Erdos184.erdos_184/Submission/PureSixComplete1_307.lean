import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_307_0 : CompleteAt 307 0 := by decide +kernel
lemma complete_307_1 : CompleteAt 307 1 := by decide +kernel
lemma complete_307_2 : CompleteAt 307 2 := by decide +kernel
lemma complete_307_3 : CompleteAt 307 3 := by decide +kernel
lemma complete_307_4 : CompleteAt 307 4 := by decide +kernel
lemma complete_case307 : ∀ e0, CompleteAt 307 e0 := by
  intro e0
  fin_cases e0
  · exact complete_307_0
  · exact complete_307_1
  · exact complete_307_2
  · exact complete_307_3
  · exact complete_307_4
#print axioms complete_case307
end Erdos184Work.PureSixLocalFilter1
