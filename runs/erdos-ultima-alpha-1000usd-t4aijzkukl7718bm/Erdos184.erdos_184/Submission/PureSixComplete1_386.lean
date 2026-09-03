import Submission.PureSixLocalFilter1
namespace Erdos184Work.PureSixLocalFilter1
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma complete_386_0 : CompleteAt 386 0 := by decide +kernel
lemma complete_386_1 : CompleteAt 386 1 := by decide +kernel
lemma complete_386_2 : CompleteAt 386 2 := by decide +kernel
lemma complete_386_3 : CompleteAt 386 3 := by decide +kernel
lemma complete_386_4 : CompleteAt 386 4 := by decide +kernel
lemma complete_case386 : ∀ e0, CompleteAt 386 e0 := by
  intro e0
  fin_cases e0
  · exact complete_386_0
  · exact complete_386_1
  · exact complete_386_2
  · exact complete_386_3
  · exact complete_386_4
#print axioms complete_case386
end Erdos184Work.PureSixLocalFilter1
