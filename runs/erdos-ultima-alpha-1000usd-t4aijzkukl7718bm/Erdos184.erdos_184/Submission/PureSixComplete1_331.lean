import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_331_0 : CompleteAt 331 0 := by decide +kernel
lemma complete_331_1 : CompleteAt 331 1 := by decide +kernel
lemma complete_331_2 : CompleteAt 331 2 := by decide +kernel
lemma complete_331_3 : CompleteAt 331 3 := by decide +kernel
lemma complete_331_4 : CompleteAt 331 4 := by decide +kernel
lemma complete_case331 : ∀ e0, CompleteAt 331 e0 := by
  intro e0
  fin_cases e0
  · exact complete_331_0
  · exact complete_331_1
  · exact complete_331_2
  · exact complete_331_3
  · exact complete_331_4
#print axioms complete_case331
end Erdos184Work.PureSixLocalFilter1
