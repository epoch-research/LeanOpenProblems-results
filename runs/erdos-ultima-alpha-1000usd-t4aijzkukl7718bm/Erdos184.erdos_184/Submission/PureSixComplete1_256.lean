import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_256_0 : CompleteAt 256 0 := by decide +kernel
lemma complete_256_1 : CompleteAt 256 1 := by decide +kernel
lemma complete_256_2 : CompleteAt 256 2 := by decide +kernel
lemma complete_256_3 : CompleteAt 256 3 := by decide +kernel
lemma complete_256_4 : CompleteAt 256 4 := by decide +kernel
lemma complete_case256 : ∀ e0, CompleteAt 256 e0 := by
  intro e0
  fin_cases e0
  · exact complete_256_0
  · exact complete_256_1
  · exact complete_256_2
  · exact complete_256_3
  · exact complete_256_4
#print axioms complete_case256
end Erdos184Work.PureSixLocalFilter1
