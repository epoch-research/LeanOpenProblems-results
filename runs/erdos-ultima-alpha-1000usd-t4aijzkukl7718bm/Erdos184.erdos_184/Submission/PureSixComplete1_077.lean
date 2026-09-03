import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_77_0 : CompleteAt 77 0 := by decide +kernel
lemma complete_77_1 : CompleteAt 77 1 := by decide +kernel
lemma complete_77_2 : CompleteAt 77 2 := by decide +kernel
lemma complete_77_3 : CompleteAt 77 3 := by decide +kernel
lemma complete_77_4 : CompleteAt 77 4 := by decide +kernel
lemma complete_case77 : ∀ e0, CompleteAt 77 e0 := by
  intro e0
  fin_cases e0
  · exact complete_77_0
  · exact complete_77_1
  · exact complete_77_2
  · exact complete_77_3
  · exact complete_77_4
#print axioms complete_case77
end Erdos184Work.PureSixLocalFilter1
