import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_390_0 : CompleteAt 390 0 := by decide +kernel
lemma complete_390_1 : CompleteAt 390 1 := by decide +kernel
lemma complete_390_2 : CompleteAt 390 2 := by decide +kernel
lemma complete_390_3 : CompleteAt 390 3 := by decide +kernel
lemma complete_390_4 : CompleteAt 390 4 := by decide +kernel
lemma complete_case390 : ∀ e0, CompleteAt 390 e0 := by
  intro e0
  fin_cases e0
  · exact complete_390_0
  · exact complete_390_1
  · exact complete_390_2
  · exact complete_390_3
  · exact complete_390_4
#print axioms complete_case390
end Erdos184Work.PureSixLocalFilter1
