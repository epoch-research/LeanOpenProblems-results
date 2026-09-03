import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_212_0 : CompleteAt 212 0 := by decide +kernel
lemma complete_212_1 : CompleteAt 212 1 := by decide +kernel
lemma complete_212_2 : CompleteAt 212 2 := by decide +kernel
lemma complete_212_3 : CompleteAt 212 3 := by decide +kernel
lemma complete_212_4 : CompleteAt 212 4 := by decide +kernel
lemma complete_case212 : ∀ e0, CompleteAt 212 e0 := by
  intro e0
  fin_cases e0
  · exact complete_212_0
  · exact complete_212_1
  · exact complete_212_2
  · exact complete_212_3
  · exact complete_212_4
#print axioms complete_case212
end Erdos184Work.PureSixLocalFilter1
