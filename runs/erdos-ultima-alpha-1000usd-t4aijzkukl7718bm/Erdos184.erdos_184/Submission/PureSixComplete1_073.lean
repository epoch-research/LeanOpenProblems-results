import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_73_0 : CompleteAt 73 0 := by decide +kernel
lemma complete_73_1 : CompleteAt 73 1 := by decide +kernel
lemma complete_73_2 : CompleteAt 73 2 := by decide +kernel
lemma complete_73_3 : CompleteAt 73 3 := by decide +kernel
lemma complete_73_4 : CompleteAt 73 4 := by decide +kernel
lemma complete_case73 : ∀ e0, CompleteAt 73 e0 := by
  intro e0
  fin_cases e0
  · exact complete_73_0
  · exact complete_73_1
  · exact complete_73_2
  · exact complete_73_3
  · exact complete_73_4
#print axioms complete_case73
end Erdos184Work.PureSixLocalFilter1
