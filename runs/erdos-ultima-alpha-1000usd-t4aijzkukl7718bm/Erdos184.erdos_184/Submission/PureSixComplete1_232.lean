import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_232_0 : CompleteAt 232 0 := by decide +kernel
lemma complete_232_1 : CompleteAt 232 1 := by decide +kernel
lemma complete_232_2 : CompleteAt 232 2 := by decide +kernel
lemma complete_232_3 : CompleteAt 232 3 := by decide +kernel
lemma complete_232_4 : CompleteAt 232 4 := by decide +kernel
lemma complete_case232 : ∀ e0, CompleteAt 232 e0 := by
  intro e0
  fin_cases e0
  · exact complete_232_0
  · exact complete_232_1
  · exact complete_232_2
  · exact complete_232_3
  · exact complete_232_4
#print axioms complete_case232
end Erdos184Work.PureSixLocalFilter1
