import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_24_0 : CompleteAt 24 0 := by decide +kernel
lemma complete_24_1 : CompleteAt 24 1 := by decide +kernel
lemma complete_24_2 : CompleteAt 24 2 := by decide +kernel
lemma complete_24_3 : CompleteAt 24 3 := by decide +kernel
lemma complete_24_4 : CompleteAt 24 4 := by decide +kernel
lemma complete_24_5 : CompleteAt 24 5 := by decide +kernel
lemma complete_case24 : ∀ e0, CompleteAt 24 e0 := by
  intro e0
  fin_cases e0
  · exact complete_24_0
  · exact complete_24_1
  · exact complete_24_2
  · exact complete_24_3
  · exact complete_24_4
  · exact complete_24_5
#print axioms complete_case24
end Erdos184Work.PureSixLocalFilter4
