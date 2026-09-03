import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_52_0 : CompleteAt 52 0 := by decide +kernel
lemma complete_52_1 : CompleteAt 52 1 := by decide +kernel
lemma complete_52_2 : CompleteAt 52 2 := by decide +kernel
lemma complete_52_3 : CompleteAt 52 3 := by decide +kernel
lemma complete_case52 : ∀ e0, CompleteAt 52 e0 := by
  intro e0
  fin_cases e0
  · exact complete_52_0
  · exact complete_52_1
  · exact complete_52_2
  · exact complete_52_3
#print axioms complete_case52
end Erdos184Work.PureSixLocalFilter0
