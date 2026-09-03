import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_63_0 : CompleteAt 63 0 := by decide +kernel
lemma complete_63_1 : CompleteAt 63 1 := by decide +kernel
lemma complete_63_2 : CompleteAt 63 2 := by decide +kernel
lemma complete_63_3 : CompleteAt 63 3 := by decide +kernel
lemma complete_63_4 : CompleteAt 63 4 := by decide +kernel
lemma complete_63_5 : CompleteAt 63 5 := by decide +kernel
lemma complete_case63 : ∀ e0, CompleteAt 63 e0 := by
  intro e0
  fin_cases e0
  · exact complete_63_0
  · exact complete_63_1
  · exact complete_63_2
  · exact complete_63_3
  · exact complete_63_4
  · exact complete_63_5
#print axioms complete_case63
end Erdos184Work.PureSixLocalFilter4
