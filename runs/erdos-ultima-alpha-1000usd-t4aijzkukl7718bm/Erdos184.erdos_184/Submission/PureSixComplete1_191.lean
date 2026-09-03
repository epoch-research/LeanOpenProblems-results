import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_191_0 : CompleteAt 191 0 := by decide +kernel
lemma complete_191_1 : CompleteAt 191 1 := by decide +kernel
lemma complete_191_2 : CompleteAt 191 2 := by decide +kernel
lemma complete_191_3 : CompleteAt 191 3 := by decide +kernel
lemma complete_191_4 : CompleteAt 191 4 := by decide +kernel
lemma complete_case191 : ∀ e0, CompleteAt 191 e0 := by
  intro e0
  fin_cases e0
  · exact complete_191_0
  · exact complete_191_1
  · exact complete_191_2
  · exact complete_191_3
  · exact complete_191_4
#print axioms complete_case191
end Erdos184Work.PureSixLocalFilter1
