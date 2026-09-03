import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_151_0 : CompleteAt 151 0 := by decide +kernel
lemma complete_151_1 : CompleteAt 151 1 := by decide +kernel
lemma complete_151_2 : CompleteAt 151 2 := by decide +kernel
lemma complete_151_3 : CompleteAt 151 3 := by decide +kernel
lemma complete_151_4 : CompleteAt 151 4 := by decide +kernel
lemma complete_case151 : ∀ e0, CompleteAt 151 e0 := by
  intro e0
  fin_cases e0
  · exact complete_151_0
  · exact complete_151_1
  · exact complete_151_2
  · exact complete_151_3
  · exact complete_151_4
#print axioms complete_case151
end Erdos184Work.PureSixLocalFilter1
