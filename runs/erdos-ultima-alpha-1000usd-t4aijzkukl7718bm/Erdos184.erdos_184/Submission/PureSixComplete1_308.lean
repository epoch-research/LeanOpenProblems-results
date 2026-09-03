import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_308_0 : CompleteAt 308 0 := by decide +kernel
lemma complete_308_1 : CompleteAt 308 1 := by decide +kernel
lemma complete_308_2 : CompleteAt 308 2 := by decide +kernel
lemma complete_308_3 : CompleteAt 308 3 := by decide +kernel
lemma complete_308_4 : CompleteAt 308 4 := by decide +kernel
lemma complete_case308 : ∀ e0, CompleteAt 308 e0 := by
  intro e0
  fin_cases e0
  · exact complete_308_0
  · exact complete_308_1
  · exact complete_308_2
  · exact complete_308_3
  · exact complete_308_4
#print axioms complete_case308
end Erdos184Work.PureSixLocalFilter1
