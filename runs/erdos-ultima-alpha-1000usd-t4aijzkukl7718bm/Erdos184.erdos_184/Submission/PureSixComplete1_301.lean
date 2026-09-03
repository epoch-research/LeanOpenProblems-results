import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_301_0 : CompleteAt 301 0 := by decide +kernel
lemma complete_301_1 : CompleteAt 301 1 := by decide +kernel
lemma complete_301_2 : CompleteAt 301 2 := by decide +kernel
lemma complete_301_3 : CompleteAt 301 3 := by decide +kernel
lemma complete_301_4 : CompleteAt 301 4 := by decide +kernel
lemma complete_case301 : ∀ e0, CompleteAt 301 e0 := by
  intro e0
  fin_cases e0
  · exact complete_301_0
  · exact complete_301_1
  · exact complete_301_2
  · exact complete_301_3
  · exact complete_301_4
#print axioms complete_case301
end Erdos184Work.PureSixLocalFilter1
