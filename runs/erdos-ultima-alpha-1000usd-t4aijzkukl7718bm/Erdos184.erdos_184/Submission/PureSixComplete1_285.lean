import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_285_0 : CompleteAt 285 0 := by decide +kernel
lemma complete_285_1 : CompleteAt 285 1 := by decide +kernel
lemma complete_285_2 : CompleteAt 285 2 := by decide +kernel
lemma complete_285_3 : CompleteAt 285 3 := by decide +kernel
lemma complete_285_4 : CompleteAt 285 4 := by decide +kernel
lemma complete_case285 : ∀ e0, CompleteAt 285 e0 := by
  intro e0
  fin_cases e0
  · exact complete_285_0
  · exact complete_285_1
  · exact complete_285_2
  · exact complete_285_3
  · exact complete_285_4
#print axioms complete_case285
end Erdos184Work.PureSixLocalFilter1
