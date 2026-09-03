import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_71_0 : CompleteAt 71 0 := by decide +kernel
lemma complete_71_1 : CompleteAt 71 1 := by decide +kernel
lemma complete_71_2 : CompleteAt 71 2 := by decide +kernel
lemma complete_71_3 : CompleteAt 71 3 := by decide +kernel
lemma complete_71_4 : CompleteAt 71 4 := by decide +kernel
lemma complete_case71 : ∀ e0, CompleteAt 71 e0 := by
  intro e0
  fin_cases e0
  · exact complete_71_0
  · exact complete_71_1
  · exact complete_71_2
  · exact complete_71_3
  · exact complete_71_4
#print axioms complete_case71
end Erdos184Work.PureSixLocalFilter1
