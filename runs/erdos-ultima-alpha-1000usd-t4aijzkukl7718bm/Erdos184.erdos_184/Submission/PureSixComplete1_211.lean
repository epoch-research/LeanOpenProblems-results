import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_211_0 : CompleteAt 211 0 := by decide +kernel
lemma complete_211_1 : CompleteAt 211 1 := by decide +kernel
lemma complete_211_2 : CompleteAt 211 2 := by decide +kernel
lemma complete_211_3 : CompleteAt 211 3 := by decide +kernel
lemma complete_211_4 : CompleteAt 211 4 := by decide +kernel
lemma complete_case211 : ∀ e0, CompleteAt 211 e0 := by
  intro e0
  fin_cases e0
  · exact complete_211_0
  · exact complete_211_1
  · exact complete_211_2
  · exact complete_211_3
  · exact complete_211_4
#print axioms complete_case211
end Erdos184Work.PureSixLocalFilter1
