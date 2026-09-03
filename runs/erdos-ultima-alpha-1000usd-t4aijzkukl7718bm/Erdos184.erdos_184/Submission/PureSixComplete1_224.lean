import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_224_0 : CompleteAt 224 0 := by decide +kernel
lemma complete_224_1 : CompleteAt 224 1 := by decide +kernel
lemma complete_224_2 : CompleteAt 224 2 := by decide +kernel
lemma complete_224_3 : CompleteAt 224 3 := by decide +kernel
lemma complete_224_4 : CompleteAt 224 4 := by decide +kernel
lemma complete_case224 : ∀ e0, CompleteAt 224 e0 := by
  intro e0
  fin_cases e0
  · exact complete_224_0
  · exact complete_224_1
  · exact complete_224_2
  · exact complete_224_3
  · exact complete_224_4
#print axioms complete_case224
end Erdos184Work.PureSixLocalFilter1
