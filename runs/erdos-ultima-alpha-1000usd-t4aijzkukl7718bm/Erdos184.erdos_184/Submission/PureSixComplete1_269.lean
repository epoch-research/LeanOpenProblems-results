import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_269_0 : CompleteAt 269 0 := by decide +kernel
lemma complete_269_1 : CompleteAt 269 1 := by decide +kernel
lemma complete_269_2 : CompleteAt 269 2 := by decide +kernel
lemma complete_269_3 : CompleteAt 269 3 := by decide +kernel
lemma complete_269_4 : CompleteAt 269 4 := by decide +kernel
lemma complete_case269 : ∀ e0, CompleteAt 269 e0 := by
  intro e0
  fin_cases e0
  · exact complete_269_0
  · exact complete_269_1
  · exact complete_269_2
  · exact complete_269_3
  · exact complete_269_4
#print axioms complete_case269
end Erdos184Work.PureSixLocalFilter1
