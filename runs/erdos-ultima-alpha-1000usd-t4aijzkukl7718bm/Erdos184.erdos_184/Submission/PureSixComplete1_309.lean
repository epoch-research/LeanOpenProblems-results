import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_309_0 : CompleteAt 309 0 := by decide +kernel
lemma complete_309_1 : CompleteAt 309 1 := by decide +kernel
lemma complete_309_2 : CompleteAt 309 2 := by decide +kernel
lemma complete_309_3 : CompleteAt 309 3 := by decide +kernel
lemma complete_309_4 : CompleteAt 309 4 := by decide +kernel
lemma complete_case309 : ∀ e0, CompleteAt 309 e0 := by
  intro e0
  fin_cases e0
  · exact complete_309_0
  · exact complete_309_1
  · exact complete_309_2
  · exact complete_309_3
  · exact complete_309_4
#print axioms complete_case309
end Erdos184Work.PureSixLocalFilter1
