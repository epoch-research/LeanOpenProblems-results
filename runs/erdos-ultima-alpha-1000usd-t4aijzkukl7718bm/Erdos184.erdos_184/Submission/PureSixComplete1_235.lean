import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_235_0 : CompleteAt 235 0 := by decide +kernel
lemma complete_235_1 : CompleteAt 235 1 := by decide +kernel
lemma complete_235_2 : CompleteAt 235 2 := by decide +kernel
lemma complete_235_3 : CompleteAt 235 3 := by decide +kernel
lemma complete_235_4 : CompleteAt 235 4 := by decide +kernel
lemma complete_case235 : ∀ e0, CompleteAt 235 e0 := by
  intro e0
  fin_cases e0
  · exact complete_235_0
  · exact complete_235_1
  · exact complete_235_2
  · exact complete_235_3
  · exact complete_235_4
#print axioms complete_case235
end Erdos184Work.PureSixLocalFilter1
