import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_96_0 : CompleteAt 96 0 := by decide +kernel
lemma complete_96_1 : CompleteAt 96 1 := by decide +kernel
lemma complete_96_2 : CompleteAt 96 2 := by decide +kernel
lemma complete_96_3 : CompleteAt 96 3 := by decide +kernel
lemma complete_96_4 : CompleteAt 96 4 := by decide +kernel
lemma complete_case96 : ∀ e0, CompleteAt 96 e0 := by
  intro e0
  fin_cases e0
  · exact complete_96_0
  · exact complete_96_1
  · exact complete_96_2
  · exact complete_96_3
  · exact complete_96_4
#print axioms complete_case96
end Erdos184Work.PureSixLocalFilter1
