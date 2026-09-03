import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_239_0 : CompleteAt 239 0 := by decide +kernel
lemma complete_239_1 : CompleteAt 239 1 := by decide +kernel
lemma complete_239_2 : CompleteAt 239 2 := by decide +kernel
lemma complete_239_3 : CompleteAt 239 3 := by decide +kernel
lemma complete_239_4 : CompleteAt 239 4 := by decide +kernel
lemma complete_case239 : ∀ e0, CompleteAt 239 e0 := by
  intro e0
  fin_cases e0
  · exact complete_239_0
  · exact complete_239_1
  · exact complete_239_2
  · exact complete_239_3
  · exact complete_239_4
#print axioms complete_case239
end Erdos184Work.PureSixLocalFilter1
