import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_139_0 : CompleteAt 139 0 := by decide +kernel
lemma complete_139_1 : CompleteAt 139 1 := by decide +kernel
lemma complete_139_2 : CompleteAt 139 2 := by decide +kernel
lemma complete_139_3 : CompleteAt 139 3 := by decide +kernel
lemma complete_139_4 : CompleteAt 139 4 := by decide +kernel
lemma complete_case139 : ∀ e0, CompleteAt 139 e0 := by
  intro e0
  fin_cases e0
  · exact complete_139_0
  · exact complete_139_1
  · exact complete_139_2
  · exact complete_139_3
  · exact complete_139_4
#print axioms complete_case139
end Erdos184Work.PureSixLocalFilter1
