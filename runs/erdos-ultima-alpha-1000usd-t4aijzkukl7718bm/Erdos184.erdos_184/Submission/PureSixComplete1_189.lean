import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_189_0 : CompleteAt 189 0 := by decide +kernel
lemma complete_189_1 : CompleteAt 189 1 := by decide +kernel
lemma complete_189_2 : CompleteAt 189 2 := by decide +kernel
lemma complete_189_3 : CompleteAt 189 3 := by decide +kernel
lemma complete_189_4 : CompleteAt 189 4 := by decide +kernel
lemma complete_case189 : ∀ e0, CompleteAt 189 e0 := by
  intro e0
  fin_cases e0
  · exact complete_189_0
  · exact complete_189_1
  · exact complete_189_2
  · exact complete_189_3
  · exact complete_189_4
#print axioms complete_case189
end Erdos184Work.PureSixLocalFilter1
