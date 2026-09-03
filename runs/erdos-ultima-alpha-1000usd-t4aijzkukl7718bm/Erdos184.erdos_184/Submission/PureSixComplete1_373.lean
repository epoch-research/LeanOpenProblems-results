import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_373_0 : CompleteAt 373 0 := by decide +kernel
lemma complete_373_1 : CompleteAt 373 1 := by decide +kernel
lemma complete_373_2 : CompleteAt 373 2 := by decide +kernel
lemma complete_373_3 : CompleteAt 373 3 := by decide +kernel
lemma complete_373_4 : CompleteAt 373 4 := by decide +kernel
lemma complete_case373 : ∀ e0, CompleteAt 373 e0 := by
  intro e0
  fin_cases e0
  · exact complete_373_0
  · exact complete_373_1
  · exact complete_373_2
  · exact complete_373_3
  · exact complete_373_4
#print axioms complete_case373
end Erdos184Work.PureSixLocalFilter1
