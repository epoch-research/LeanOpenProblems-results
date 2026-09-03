import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_215_0 : CompleteAt 215 0 := by decide +kernel
lemma complete_215_1 : CompleteAt 215 1 := by decide +kernel
lemma complete_215_2 : CompleteAt 215 2 := by decide +kernel
lemma complete_215_3 : CompleteAt 215 3 := by decide +kernel
lemma complete_215_4 : CompleteAt 215 4 := by decide +kernel
lemma complete_case215 : ∀ e0, CompleteAt 215 e0 := by
  intro e0
  fin_cases e0
  · exact complete_215_0
  · exact complete_215_1
  · exact complete_215_2
  · exact complete_215_3
  · exact complete_215_4
#print axioms complete_case215
end Erdos184Work.PureSixLocalFilter1
