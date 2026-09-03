import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_378_0 : CompleteAt 378 0 := by decide +kernel
lemma complete_378_1 : CompleteAt 378 1 := by decide +kernel
lemma complete_378_2 : CompleteAt 378 2 := by decide +kernel
lemma complete_378_3 : CompleteAt 378 3 := by decide +kernel
lemma complete_378_4 : CompleteAt 378 4 := by decide +kernel
lemma complete_case378 : ∀ e0, CompleteAt 378 e0 := by
  intro e0
  fin_cases e0
  · exact complete_378_0
  · exact complete_378_1
  · exact complete_378_2
  · exact complete_378_3
  · exact complete_378_4
#print axioms complete_case378
end Erdos184Work.PureSixLocalFilter1
