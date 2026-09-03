import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_150_0 : CompleteAt 150 0 := by decide +kernel
lemma complete_150_1 : CompleteAt 150 1 := by decide +kernel
lemma complete_150_2 : CompleteAt 150 2 := by decide +kernel
lemma complete_150_3 : CompleteAt 150 3 := by decide +kernel
lemma complete_150_4 : CompleteAt 150 4 := by decide +kernel
lemma complete_case150 : ∀ e0, CompleteAt 150 e0 := by
  intro e0
  fin_cases e0
  · exact complete_150_0
  · exact complete_150_1
  · exact complete_150_2
  · exact complete_150_3
  · exact complete_150_4
#print axioms complete_case150
end Erdos184Work.PureSixLocalFilter1
