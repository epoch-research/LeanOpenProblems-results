import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_78_0 : CompleteAt 78 0 := by decide +kernel
lemma complete_78_1 : CompleteAt 78 1 := by decide +kernel
lemma complete_78_2 : CompleteAt 78 2 := by decide +kernel
lemma complete_78_3 : CompleteAt 78 3 := by decide +kernel
lemma complete_case78 : ∀ e0, CompleteAt 78 e0 := by
  intro e0
  fin_cases e0
  · exact complete_78_0
  · exact complete_78_1
  · exact complete_78_2
  · exact complete_78_3
#print axioms complete_case78
end Erdos184Work.PureSixLocalFilter0
