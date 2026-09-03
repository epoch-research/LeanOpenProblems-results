import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_289_0 : CompleteAt 289 0 := by decide +kernel
lemma complete_289_1 : CompleteAt 289 1 := by decide +kernel
lemma complete_289_2 : CompleteAt 289 2 := by decide +kernel
lemma complete_289_3 : CompleteAt 289 3 := by decide +kernel
lemma complete_289_4 : CompleteAt 289 4 := by decide +kernel
lemma complete_case289 : ∀ e0, CompleteAt 289 e0 := by
  intro e0
  fin_cases e0
  · exact complete_289_0
  · exact complete_289_1
  · exact complete_289_2
  · exact complete_289_3
  · exact complete_289_4
#print axioms complete_case289
end Erdos184Work.PureSixLocalFilter1
