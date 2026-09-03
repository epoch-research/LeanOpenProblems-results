import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_78_0 : CompleteAt 78 0 := by decide +kernel
lemma complete_78_1 : CompleteAt 78 1 := by decide +kernel
lemma complete_78_2 : CompleteAt 78 2 := by decide +kernel
lemma complete_78_3 : CompleteAt 78 3 := by decide +kernel
lemma complete_78_4 : CompleteAt 78 4 := by decide +kernel
lemma complete_78_5 : CompleteAt 78 5 := by decide +kernel
lemma complete_case78 : ∀ e0, CompleteAt 78 e0 := by
  intro e0
  fin_cases e0
  · exact complete_78_0
  · exact complete_78_1
  · exact complete_78_2
  · exact complete_78_3
  · exact complete_78_4
  · exact complete_78_5
#print axioms complete_case78
end Erdos184Work.PureSixLocalFilter4
