import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_216_0 : CompleteAt 216 0 := by decide +kernel
lemma complete_216_1 : CompleteAt 216 1 := by decide +kernel
lemma complete_216_2 : CompleteAt 216 2 := by decide +kernel
lemma complete_216_3 : CompleteAt 216 3 := by decide +kernel
lemma complete_216_4 : CompleteAt 216 4 := by decide +kernel
lemma complete_case216 : ∀ e0, CompleteAt 216 e0 := by
  intro e0
  fin_cases e0
  · exact complete_216_0
  · exact complete_216_1
  · exact complete_216_2
  · exact complete_216_3
  · exact complete_216_4
#print axioms complete_case216
end Erdos184Work.PureSixLocalFilter1
