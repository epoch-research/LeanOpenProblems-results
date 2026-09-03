import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_356_0 : CompleteAt 356 0 := by decide +kernel
lemma complete_356_1 : CompleteAt 356 1 := by decide +kernel
lemma complete_356_2 : CompleteAt 356 2 := by decide +kernel
lemma complete_356_3 : CompleteAt 356 3 := by decide +kernel
lemma complete_356_4 : CompleteAt 356 4 := by decide +kernel
lemma complete_case356 : ∀ e0, CompleteAt 356 e0 := by
  intro e0
  fin_cases e0
  · exact complete_356_0
  · exact complete_356_1
  · exact complete_356_2
  · exact complete_356_3
  · exact complete_356_4
#print axioms complete_case356
end Erdos184Work.PureSixLocalFilter1
