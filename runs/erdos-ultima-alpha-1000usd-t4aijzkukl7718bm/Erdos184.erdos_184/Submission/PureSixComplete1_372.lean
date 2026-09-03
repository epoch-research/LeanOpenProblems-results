import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_372_0 : CompleteAt 372 0 := by decide +kernel
lemma complete_372_1 : CompleteAt 372 1 := by decide +kernel
lemma complete_372_2 : CompleteAt 372 2 := by decide +kernel
lemma complete_372_3 : CompleteAt 372 3 := by decide +kernel
lemma complete_372_4 : CompleteAt 372 4 := by decide +kernel
lemma complete_case372 : ∀ e0, CompleteAt 372 e0 := by
  intro e0
  fin_cases e0
  · exact complete_372_0
  · exact complete_372_1
  · exact complete_372_2
  · exact complete_372_3
  · exact complete_372_4
#print axioms complete_case372
end Erdos184Work.PureSixLocalFilter1
