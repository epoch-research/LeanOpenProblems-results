import Submission.PureSixLocalFilter0
namespace Erdos184Work.PureSixLocalFilter0
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_144_0 : CompleteAt 144 0 := by decide +kernel
lemma complete_144_1 : CompleteAt 144 1 := by decide +kernel
lemma complete_144_2 : CompleteAt 144 2 := by decide +kernel
lemma complete_144_3 : CompleteAt 144 3 := by decide +kernel
lemma complete_case144 : ∀ e0, CompleteAt 144 e0 := by
  intro e0
  fin_cases e0
  · exact complete_144_0
  · exact complete_144_1
  · exact complete_144_2
  · exact complete_144_3
#print axioms complete_case144
end Erdos184Work.PureSixLocalFilter0
