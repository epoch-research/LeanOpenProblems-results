import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_313_0 : CompleteAt 313 0 := by decide +kernel
lemma complete_313_1 : CompleteAt 313 1 := by decide +kernel
lemma complete_313_2 : CompleteAt 313 2 := by decide +kernel
lemma complete_313_3 : CompleteAt 313 3 := by decide +kernel
lemma complete_313_4 : CompleteAt 313 4 := by decide +kernel
lemma complete_case313 : ∀ e0, CompleteAt 313 e0 := by
  intro e0
  fin_cases e0
  · exact complete_313_0
  · exact complete_313_1
  · exact complete_313_2
  · exact complete_313_3
  · exact complete_313_4
#print axioms complete_case313
end Erdos184Work.PureSixLocalFilter1
