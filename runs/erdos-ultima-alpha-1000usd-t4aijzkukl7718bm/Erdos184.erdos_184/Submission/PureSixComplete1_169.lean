import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_169_0 : CompleteAt 169 0 := by decide +kernel
lemma complete_169_1 : CompleteAt 169 1 := by decide +kernel
lemma complete_169_2 : CompleteAt 169 2 := by decide +kernel
lemma complete_169_3 : CompleteAt 169 3 := by decide +kernel
lemma complete_169_4 : CompleteAt 169 4 := by decide +kernel
lemma complete_case169 : ∀ e0, CompleteAt 169 e0 := by
  intro e0
  fin_cases e0
  · exact complete_169_0
  · exact complete_169_1
  · exact complete_169_2
  · exact complete_169_3
  · exact complete_169_4
#print axioms complete_case169
end Erdos184Work.PureSixLocalFilter1
