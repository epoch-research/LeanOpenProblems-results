import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_340_0 : CompleteAt 340 0 := by decide +kernel
lemma complete_340_1 : CompleteAt 340 1 := by decide +kernel
lemma complete_340_2 : CompleteAt 340 2 := by decide +kernel
lemma complete_340_3 : CompleteAt 340 3 := by decide +kernel
lemma complete_340_4 : CompleteAt 340 4 := by decide +kernel
lemma complete_case340 : ∀ e0, CompleteAt 340 e0 := by
  intro e0
  fin_cases e0
  · exact complete_340_0
  · exact complete_340_1
  · exact complete_340_2
  · exact complete_340_3
  · exact complete_340_4
#print axioms complete_case340
end Erdos184Work.PureSixLocalFilter1
