import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_67_0 : CompleteAt 67 0 := by decide +kernel
lemma complete_67_1 : CompleteAt 67 1 := by decide +kernel
lemma complete_67_2 : CompleteAt 67 2 := by decide +kernel
lemma complete_67_3 : CompleteAt 67 3 := by decide +kernel
lemma complete_67_4 : CompleteAt 67 4 := by decide +kernel
lemma complete_case67 : ∀ e0, CompleteAt 67 e0 := by
  intro e0
  fin_cases e0
  · exact complete_67_0
  · exact complete_67_1
  · exact complete_67_2
  · exact complete_67_3
  · exact complete_67_4
#print axioms complete_case67
end Erdos184Work.PureSixLocalFilter1
