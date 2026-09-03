import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_111_0 : CompleteAt 111 0 := by decide +kernel
lemma complete_111_1 : CompleteAt 111 1 := by decide +kernel
lemma complete_111_2 : CompleteAt 111 2 := by decide +kernel
lemma complete_111_3 : CompleteAt 111 3 := by decide +kernel
lemma complete_111_4 : CompleteAt 111 4 := by decide +kernel
lemma complete_case111 : ∀ e0, CompleteAt 111 e0 := by
  intro e0
  fin_cases e0
  · exact complete_111_0
  · exact complete_111_1
  · exact complete_111_2
  · exact complete_111_3
  · exact complete_111_4
#print axioms complete_case111
end Erdos184Work.PureSixLocalFilter1
