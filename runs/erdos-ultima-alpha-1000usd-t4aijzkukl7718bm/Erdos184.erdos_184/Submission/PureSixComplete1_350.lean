import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_350_0 : CompleteAt 350 0 := by decide +kernel
lemma complete_350_1 : CompleteAt 350 1 := by decide +kernel
lemma complete_350_2 : CompleteAt 350 2 := by decide +kernel
lemma complete_350_3 : CompleteAt 350 3 := by decide +kernel
lemma complete_350_4 : CompleteAt 350 4 := by decide +kernel
lemma complete_case350 : ∀ e0, CompleteAt 350 e0 := by
  intro e0
  fin_cases e0
  · exact complete_350_0
  · exact complete_350_1
  · exact complete_350_2
  · exact complete_350_3
  · exact complete_350_4
#print axioms complete_case350
end Erdos184Work.PureSixLocalFilter1
