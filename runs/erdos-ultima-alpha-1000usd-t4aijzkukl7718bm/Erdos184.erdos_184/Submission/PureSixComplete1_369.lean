import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_369_0 : CompleteAt 369 0 := by decide +kernel
lemma complete_369_1 : CompleteAt 369 1 := by decide +kernel
lemma complete_369_2 : CompleteAt 369 2 := by decide +kernel
lemma complete_369_3 : CompleteAt 369 3 := by decide +kernel
lemma complete_369_4 : CompleteAt 369 4 := by decide +kernel
lemma complete_case369 : ∀ e0, CompleteAt 369 e0 := by
  intro e0
  fin_cases e0
  · exact complete_369_0
  · exact complete_369_1
  · exact complete_369_2
  · exact complete_369_3
  · exact complete_369_4
#print axioms complete_case369
end Erdos184Work.PureSixLocalFilter1
