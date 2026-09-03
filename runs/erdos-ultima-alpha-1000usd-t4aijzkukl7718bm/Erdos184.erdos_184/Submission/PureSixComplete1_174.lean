import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_174_0 : CompleteAt 174 0 := by decide +kernel
lemma complete_174_1 : CompleteAt 174 1 := by decide +kernel
lemma complete_174_2 : CompleteAt 174 2 := by decide +kernel
lemma complete_174_3 : CompleteAt 174 3 := by decide +kernel
lemma complete_174_4 : CompleteAt 174 4 := by decide +kernel
lemma complete_case174 : ∀ e0, CompleteAt 174 e0 := by
  intro e0
  fin_cases e0
  · exact complete_174_0
  · exact complete_174_1
  · exact complete_174_2
  · exact complete_174_3
  · exact complete_174_4
#print axioms complete_case174
end Erdos184Work.PureSixLocalFilter1
