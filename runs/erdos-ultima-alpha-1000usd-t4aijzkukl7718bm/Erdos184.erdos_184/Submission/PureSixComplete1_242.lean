import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_242_0 : CompleteAt 242 0 := by decide +kernel
lemma complete_242_1 : CompleteAt 242 1 := by decide +kernel
lemma complete_242_2 : CompleteAt 242 2 := by decide +kernel
lemma complete_242_3 : CompleteAt 242 3 := by decide +kernel
lemma complete_242_4 : CompleteAt 242 4 := by decide +kernel
lemma complete_case242 : ∀ e0, CompleteAt 242 e0 := by
  intro e0
  fin_cases e0
  · exact complete_242_0
  · exact complete_242_1
  · exact complete_242_2
  · exact complete_242_3
  · exact complete_242_4
#print axioms complete_case242
end Erdos184Work.PureSixLocalFilter1
