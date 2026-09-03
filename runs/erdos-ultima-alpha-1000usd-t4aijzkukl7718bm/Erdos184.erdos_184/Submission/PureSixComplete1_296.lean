import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_296_0 : CompleteAt 296 0 := by decide +kernel
lemma complete_296_1 : CompleteAt 296 1 := by decide +kernel
lemma complete_296_2 : CompleteAt 296 2 := by decide +kernel
lemma complete_296_3 : CompleteAt 296 3 := by decide +kernel
lemma complete_296_4 : CompleteAt 296 4 := by decide +kernel
lemma complete_case296 : ∀ e0, CompleteAt 296 e0 := by
  intro e0
  fin_cases e0
  · exact complete_296_0
  · exact complete_296_1
  · exact complete_296_2
  · exact complete_296_3
  · exact complete_296_4
#print axioms complete_case296
end Erdos184Work.PureSixLocalFilter1
