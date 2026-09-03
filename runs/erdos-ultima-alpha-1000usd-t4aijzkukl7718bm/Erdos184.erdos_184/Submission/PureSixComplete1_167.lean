import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_167_0 : CompleteAt 167 0 := by decide +kernel
lemma complete_167_1 : CompleteAt 167 1 := by decide +kernel
lemma complete_167_2 : CompleteAt 167 2 := by decide +kernel
lemma complete_167_3 : CompleteAt 167 3 := by decide +kernel
lemma complete_167_4 : CompleteAt 167 4 := by decide +kernel
lemma complete_case167 : ∀ e0, CompleteAt 167 e0 := by
  intro e0
  fin_cases e0
  · exact complete_167_0
  · exact complete_167_1
  · exact complete_167_2
  · exact complete_167_3
  · exact complete_167_4
#print axioms complete_case167
end Erdos184Work.PureSixLocalFilter1
