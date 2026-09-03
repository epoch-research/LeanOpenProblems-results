import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_258_0 : CompleteAt 258 0 := by decide +kernel
lemma complete_258_1 : CompleteAt 258 1 := by decide +kernel
lemma complete_258_2 : CompleteAt 258 2 := by decide +kernel
lemma complete_258_3 : CompleteAt 258 3 := by decide +kernel
lemma complete_258_4 : CompleteAt 258 4 := by decide +kernel
lemma complete_case258 : ∀ e0, CompleteAt 258 e0 := by
  intro e0
  fin_cases e0
  · exact complete_258_0
  · exact complete_258_1
  · exact complete_258_2
  · exact complete_258_3
  · exact complete_258_4
#print axioms complete_case258
end Erdos184Work.PureSixLocalFilter1
