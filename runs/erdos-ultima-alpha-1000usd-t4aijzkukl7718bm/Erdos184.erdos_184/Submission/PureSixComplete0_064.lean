import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_64_0 : CompleteAt 64 0 := by decide +kernel
lemma complete_64_1 : CompleteAt 64 1 := by decide +kernel
lemma complete_64_2 : CompleteAt 64 2 := by decide +kernel
lemma complete_64_3 : CompleteAt 64 3 := by decide +kernel
lemma complete_case64 : ∀ e0, CompleteAt 64 e0 := by
  intro e0
  fin_cases e0
  · exact complete_64_0
  · exact complete_64_1
  · exact complete_64_2
  · exact complete_64_3
#print axioms complete_case64
end Erdos184Work.PureSixLocalFilter0
