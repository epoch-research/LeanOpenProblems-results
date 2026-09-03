import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_100_0 : CompleteAt 100 0 := by decide +kernel
lemma complete_100_1 : CompleteAt 100 1 := by decide +kernel
lemma complete_100_2 : CompleteAt 100 2 := by decide +kernel
lemma complete_100_3 : CompleteAt 100 3 := by decide +kernel
lemma complete_100_4 : CompleteAt 100 4 := by decide +kernel
lemma complete_case100 : ∀ e0, CompleteAt 100 e0 := by
  intro e0
  fin_cases e0
  · exact complete_100_0
  · exact complete_100_1
  · exact complete_100_2
  · exact complete_100_3
  · exact complete_100_4
#print axioms complete_case100
end Erdos184Work.PureSixLocalFilter1
