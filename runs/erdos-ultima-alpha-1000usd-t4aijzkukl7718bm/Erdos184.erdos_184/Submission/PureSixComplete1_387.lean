import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_387_0 : CompleteAt 387 0 := by decide +kernel
lemma complete_387_1 : CompleteAt 387 1 := by decide +kernel
lemma complete_387_2 : CompleteAt 387 2 := by decide +kernel
lemma complete_387_3 : CompleteAt 387 3 := by decide +kernel
lemma complete_387_4 : CompleteAt 387 4 := by decide +kernel
lemma complete_case387 : ∀ e0, CompleteAt 387 e0 := by
  intro e0
  fin_cases e0
  · exact complete_387_0
  · exact complete_387_1
  · exact complete_387_2
  · exact complete_387_3
  · exact complete_387_4
#print axioms complete_case387
end Erdos184Work.PureSixLocalFilter1
