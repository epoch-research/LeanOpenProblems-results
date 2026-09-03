import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_62_0 : CompleteAt 62 0 := by decide +kernel
lemma complete_62_1 : CompleteAt 62 1 := by decide +kernel
lemma complete_62_2 : CompleteAt 62 2 := by decide +kernel
lemma complete_62_3 : CompleteAt 62 3 := by decide +kernel
lemma complete_62_4 : CompleteAt 62 4 := by decide +kernel
lemma complete_62_5 : CompleteAt 62 5 := by decide +kernel
lemma complete_case62 : ∀ e0, CompleteAt 62 e0 := by
  intro e0
  fin_cases e0
  · exact complete_62_0
  · exact complete_62_1
  · exact complete_62_2
  · exact complete_62_3
  · exact complete_62_4
  · exact complete_62_5
#print axioms complete_case62
end Erdos184Work.PureSixLocalFilter4
