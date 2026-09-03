import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_201_0 : CompleteAt 201 0 := by decide +kernel
lemma complete_201_1 : CompleteAt 201 1 := by decide +kernel
lemma complete_201_2 : CompleteAt 201 2 := by decide +kernel
lemma complete_201_3 : CompleteAt 201 3 := by decide +kernel
lemma complete_201_4 : CompleteAt 201 4 := by decide +kernel
lemma complete_case201 : ∀ e0, CompleteAt 201 e0 := by
  intro e0
  fin_cases e0
  · exact complete_201_0
  · exact complete_201_1
  · exact complete_201_2
  · exact complete_201_3
  · exact complete_201_4
#print axioms complete_case201
end Erdos184Work.PureSixLocalFilter1
