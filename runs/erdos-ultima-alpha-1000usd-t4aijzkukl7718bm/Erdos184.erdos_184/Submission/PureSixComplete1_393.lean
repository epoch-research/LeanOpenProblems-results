import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_393_0 : CompleteAt 393 0 := by decide +kernel
lemma complete_393_1 : CompleteAt 393 1 := by decide +kernel
lemma complete_393_2 : CompleteAt 393 2 := by decide +kernel
lemma complete_393_3 : CompleteAt 393 3 := by decide +kernel
lemma complete_393_4 : CompleteAt 393 4 := by decide +kernel
lemma complete_case393 : ∀ e0, CompleteAt 393 e0 := by
  intro e0
  fin_cases e0
  · exact complete_393_0
  · exact complete_393_1
  · exact complete_393_2
  · exact complete_393_3
  · exact complete_393_4
#print axioms complete_case393
end Erdos184Work.PureSixLocalFilter1
