import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_272_0 : CompleteAt 272 0 := by decide +kernel
lemma complete_272_1 : CompleteAt 272 1 := by decide +kernel
lemma complete_272_2 : CompleteAt 272 2 := by decide +kernel
lemma complete_272_3 : CompleteAt 272 3 := by decide +kernel
lemma complete_272_4 : CompleteAt 272 4 := by decide +kernel
lemma complete_case272 : ∀ e0, CompleteAt 272 e0 := by
  intro e0
  fin_cases e0
  · exact complete_272_0
  · exact complete_272_1
  · exact complete_272_2
  · exact complete_272_3
  · exact complete_272_4
#print axioms complete_case272
end Erdos184Work.PureSixLocalFilter1
