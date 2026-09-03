import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_185_0 : CompleteAt 185 0 := by decide +kernel
lemma complete_185_1 : CompleteAt 185 1 := by decide +kernel
lemma complete_185_2 : CompleteAt 185 2 := by decide +kernel
lemma complete_185_3 : CompleteAt 185 3 := by decide +kernel
lemma complete_185_4 : CompleteAt 185 4 := by decide +kernel
lemma complete_case185 : ∀ e0, CompleteAt 185 e0 := by
  intro e0
  fin_cases e0
  · exact complete_185_0
  · exact complete_185_1
  · exact complete_185_2
  · exact complete_185_3
  · exact complete_185_4
#print axioms complete_case185
end Erdos184Work.PureSixLocalFilter1
