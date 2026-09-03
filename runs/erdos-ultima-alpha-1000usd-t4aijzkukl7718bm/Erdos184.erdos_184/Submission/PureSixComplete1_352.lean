import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_352_0 : CompleteAt 352 0 := by decide +kernel
lemma complete_352_1 : CompleteAt 352 1 := by decide +kernel
lemma complete_352_2 : CompleteAt 352 2 := by decide +kernel
lemma complete_352_3 : CompleteAt 352 3 := by decide +kernel
lemma complete_352_4 : CompleteAt 352 4 := by decide +kernel
lemma complete_case352 : ∀ e0, CompleteAt 352 e0 := by
  intro e0
  fin_cases e0
  · exact complete_352_0
  · exact complete_352_1
  · exact complete_352_2
  · exact complete_352_3
  · exact complete_352_4
#print axioms complete_case352
end Erdos184Work.PureSixLocalFilter1
