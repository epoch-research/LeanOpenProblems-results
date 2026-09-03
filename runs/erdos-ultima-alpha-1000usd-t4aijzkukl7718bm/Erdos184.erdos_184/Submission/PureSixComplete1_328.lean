import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_328_0 : CompleteAt 328 0 := by decide +kernel
lemma complete_328_1 : CompleteAt 328 1 := by decide +kernel
lemma complete_328_2 : CompleteAt 328 2 := by decide +kernel
lemma complete_328_3 : CompleteAt 328 3 := by decide +kernel
lemma complete_328_4 : CompleteAt 328 4 := by decide +kernel
lemma complete_case328 : ∀ e0, CompleteAt 328 e0 := by
  intro e0
  fin_cases e0
  · exact complete_328_0
  · exact complete_328_1
  · exact complete_328_2
  · exact complete_328_3
  · exact complete_328_4
#print axioms complete_case328
end Erdos184Work.PureSixLocalFilter1
