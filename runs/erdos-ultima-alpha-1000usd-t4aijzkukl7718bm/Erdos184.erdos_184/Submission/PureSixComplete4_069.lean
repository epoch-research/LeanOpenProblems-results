import Submission.PureSixLocalFilter4
namespace Erdos184Work.PureSixLocalFilter4
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_69_0 : CompleteAt 69 0 := by decide +kernel
lemma complete_69_1 : CompleteAt 69 1 := by decide +kernel
lemma complete_69_2 : CompleteAt 69 2 := by decide +kernel
lemma complete_69_3 : CompleteAt 69 3 := by decide +kernel
lemma complete_69_4 : CompleteAt 69 4 := by decide +kernel
lemma complete_69_5 : CompleteAt 69 5 := by decide +kernel
lemma complete_case69 : ∀ e0, CompleteAt 69 e0 := by
  intro e0
  fin_cases e0
  · exact complete_69_0
  · exact complete_69_1
  · exact complete_69_2
  · exact complete_69_3
  · exact complete_69_4
  · exact complete_69_5
#print axioms complete_case69
end Erdos184Work.PureSixLocalFilter4
