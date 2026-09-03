import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_388_0 : CompleteAt 388 0 := by decide +kernel
lemma complete_388_1 : CompleteAt 388 1 := by decide +kernel
lemma complete_388_2 : CompleteAt 388 2 := by decide +kernel
lemma complete_388_3 : CompleteAt 388 3 := by decide +kernel
lemma complete_388_4 : CompleteAt 388 4 := by decide +kernel
lemma complete_case388 : ∀ e0, CompleteAt 388 e0 := by
  intro e0
  fin_cases e0
  · exact complete_388_0
  · exact complete_388_1
  · exact complete_388_2
  · exact complete_388_3
  · exact complete_388_4
#print axioms complete_case388
end Erdos184Work.PureSixLocalFilter1
