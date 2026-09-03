import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_121_0 : CompleteAt 121 0 := by decide +kernel
lemma complete_121_1 : CompleteAt 121 1 := by decide +kernel
lemma complete_121_2 : CompleteAt 121 2 := by decide +kernel
lemma complete_121_3 : CompleteAt 121 3 := by decide +kernel
lemma complete_121_4 : CompleteAt 121 4 := by decide +kernel
lemma complete_case121 : ∀ e0, CompleteAt 121 e0 := by
  intro e0
  fin_cases e0
  · exact complete_121_0
  · exact complete_121_1
  · exact complete_121_2
  · exact complete_121_3
  · exact complete_121_4
#print axioms complete_case121
end Erdos184Work.PureSixLocalFilter1
