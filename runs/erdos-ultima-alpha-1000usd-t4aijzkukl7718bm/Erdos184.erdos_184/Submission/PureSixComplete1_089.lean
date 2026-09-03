import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_89_0 : CompleteAt 89 0 := by decide +kernel
lemma complete_89_1 : CompleteAt 89 1 := by decide +kernel
lemma complete_89_2 : CompleteAt 89 2 := by decide +kernel
lemma complete_89_3 : CompleteAt 89 3 := by decide +kernel
lemma complete_89_4 : CompleteAt 89 4 := by decide +kernel
lemma complete_case89 : ∀ e0, CompleteAt 89 e0 := by
  intro e0
  fin_cases e0
  · exact complete_89_0
  · exact complete_89_1
  · exact complete_89_2
  · exact complete_89_3
  · exact complete_89_4
#print axioms complete_case89
end Erdos184Work.PureSixLocalFilter1
