import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_55_0 : CompleteAt 55 0 := by decide +kernel
lemma complete_55_1 : CompleteAt 55 1 := by decide +kernel
lemma complete_55_2 : CompleteAt 55 2 := by decide +kernel
lemma complete_55_3 : CompleteAt 55 3 := by decide +kernel
lemma complete_55_4 : CompleteAt 55 4 := by decide +kernel
lemma complete_55_5 : CompleteAt 55 5 := by decide +kernel
lemma complete_case55 : ∀ e0, CompleteAt 55 e0 := by
  intro e0
  fin_cases e0
  · exact complete_55_0
  · exact complete_55_1
  · exact complete_55_2
  · exact complete_55_3
  · exact complete_55_4
  · exact complete_55_5
#print axioms complete_case55
end Erdos184Work.PureSixLocalFilter4
