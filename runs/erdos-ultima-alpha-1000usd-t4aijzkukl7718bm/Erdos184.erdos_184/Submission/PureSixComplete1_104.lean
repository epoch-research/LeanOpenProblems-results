import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_104_0 : CompleteAt 104 0 := by decide +kernel
lemma complete_104_1 : CompleteAt 104 1 := by decide +kernel
lemma complete_104_2 : CompleteAt 104 2 := by decide +kernel
lemma complete_104_3 : CompleteAt 104 3 := by decide +kernel
lemma complete_104_4 : CompleteAt 104 4 := by decide +kernel
lemma complete_case104 : ∀ e0, CompleteAt 104 e0 := by
  intro e0
  fin_cases e0
  · exact complete_104_0
  · exact complete_104_1
  · exact complete_104_2
  · exact complete_104_3
  · exact complete_104_4
#print axioms complete_case104
end Erdos184Work.PureSixLocalFilter1
