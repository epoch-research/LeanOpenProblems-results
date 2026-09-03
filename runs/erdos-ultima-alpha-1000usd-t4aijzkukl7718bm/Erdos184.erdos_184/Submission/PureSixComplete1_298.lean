import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_298_0 : CompleteAt 298 0 := by decide +kernel
lemma complete_298_1 : CompleteAt 298 1 := by decide +kernel
lemma complete_298_2 : CompleteAt 298 2 := by decide +kernel
lemma complete_298_3 : CompleteAt 298 3 := by decide +kernel
lemma complete_298_4 : CompleteAt 298 4 := by decide +kernel
lemma complete_case298 : ∀ e0, CompleteAt 298 e0 := by
  intro e0
  fin_cases e0
  · exact complete_298_0
  · exact complete_298_1
  · exact complete_298_2
  · exact complete_298_3
  · exact complete_298_4
#print axioms complete_case298
end Erdos184Work.PureSixLocalFilter1
