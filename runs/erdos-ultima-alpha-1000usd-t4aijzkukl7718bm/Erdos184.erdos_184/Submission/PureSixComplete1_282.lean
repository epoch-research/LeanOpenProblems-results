import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_282_0 : CompleteAt 282 0 := by decide +kernel
lemma complete_282_1 : CompleteAt 282 1 := by decide +kernel
lemma complete_282_2 : CompleteAt 282 2 := by decide +kernel
lemma complete_282_3 : CompleteAt 282 3 := by decide +kernel
lemma complete_282_4 : CompleteAt 282 4 := by decide +kernel
lemma complete_case282 : ∀ e0, CompleteAt 282 e0 := by
  intro e0
  fin_cases e0
  · exact complete_282_0
  · exact complete_282_1
  · exact complete_282_2
  · exact complete_282_3
  · exact complete_282_4
#print axioms complete_case282
end Erdos184Work.PureSixLocalFilter1
