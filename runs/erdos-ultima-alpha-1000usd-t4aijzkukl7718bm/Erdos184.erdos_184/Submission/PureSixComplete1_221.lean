import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_221_0 : CompleteAt 221 0 := by decide +kernel
lemma complete_221_1 : CompleteAt 221 1 := by decide +kernel
lemma complete_221_2 : CompleteAt 221 2 := by decide +kernel
lemma complete_221_3 : CompleteAt 221 3 := by decide +kernel
lemma complete_221_4 : CompleteAt 221 4 := by decide +kernel
lemma complete_case221 : ∀ e0, CompleteAt 221 e0 := by
  intro e0
  fin_cases e0
  · exact complete_221_0
  · exact complete_221_1
  · exact complete_221_2
  · exact complete_221_3
  · exact complete_221_4
#print axioms complete_case221
end Erdos184Work.PureSixLocalFilter1
