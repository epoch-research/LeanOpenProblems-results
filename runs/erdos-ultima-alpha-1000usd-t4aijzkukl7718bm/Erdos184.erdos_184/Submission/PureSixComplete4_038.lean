import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_38_0 : CompleteAt 38 0 := by decide +kernel
lemma complete_38_1 : CompleteAt 38 1 := by decide +kernel
lemma complete_38_2 : CompleteAt 38 2 := by decide +kernel
lemma complete_38_3 : CompleteAt 38 3 := by decide +kernel
lemma complete_38_4 : CompleteAt 38 4 := by decide +kernel
lemma complete_38_5 : CompleteAt 38 5 := by decide +kernel
lemma complete_case38 : ∀ e0, CompleteAt 38 e0 := by
  intro e0
  fin_cases e0
  · exact complete_38_0
  · exact complete_38_1
  · exact complete_38_2
  · exact complete_38_3
  · exact complete_38_4
  · exact complete_38_5
#print axioms complete_case38
end Erdos184Work.PureSixLocalFilter4
