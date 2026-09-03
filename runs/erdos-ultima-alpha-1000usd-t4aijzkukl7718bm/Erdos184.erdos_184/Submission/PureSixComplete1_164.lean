import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_164_0 : CompleteAt 164 0 := by decide +kernel
lemma complete_164_1 : CompleteAt 164 1 := by decide +kernel
lemma complete_164_2 : CompleteAt 164 2 := by decide +kernel
lemma complete_164_3 : CompleteAt 164 3 := by decide +kernel
lemma complete_164_4 : CompleteAt 164 4 := by decide +kernel
lemma complete_case164 : ∀ e0, CompleteAt 164 e0 := by
  intro e0
  fin_cases e0
  · exact complete_164_0
  · exact complete_164_1
  · exact complete_164_2
  · exact complete_164_3
  · exact complete_164_4
#print axioms complete_case164
end Erdos184Work.PureSixLocalFilter1
