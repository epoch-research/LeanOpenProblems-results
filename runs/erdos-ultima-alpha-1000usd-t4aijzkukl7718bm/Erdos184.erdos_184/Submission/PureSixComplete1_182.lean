import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_182_0 : CompleteAt 182 0 := by decide +kernel
lemma complete_182_1 : CompleteAt 182 1 := by decide +kernel
lemma complete_182_2 : CompleteAt 182 2 := by decide +kernel
lemma complete_182_3 : CompleteAt 182 3 := by decide +kernel
lemma complete_182_4 : CompleteAt 182 4 := by decide +kernel
lemma complete_case182 : ∀ e0, CompleteAt 182 e0 := by
  intro e0
  fin_cases e0
  · exact complete_182_0
  · exact complete_182_1
  · exact complete_182_2
  · exact complete_182_3
  · exact complete_182_4
#print axioms complete_case182
end Erdos184Work.PureSixLocalFilter1
