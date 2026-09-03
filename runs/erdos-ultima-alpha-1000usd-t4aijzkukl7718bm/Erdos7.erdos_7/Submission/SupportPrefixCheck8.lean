import Submission.SupportPrefixCheckDefs
/-! Kernel-checked integer rows for an auxiliary prefix certificate. -/
namespace Erdos7SupportPrefixChecks
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem lower_block8 : ∀ i : Fin 4, ∀ j : Fin 180, lowerRow (i.val+32) j := by decide +kernel
theorem moment_block8 : ∀ i : Fin 4, ∀ j : Fin 10, momentRow (i.val+32) j := by decide +kernel
theorem loss_block8 : ∀ i : Fin 4, lossRow (i.val+32) := by decide +kernel
#print axioms lower_block8
#print axioms moment_block8
#print axioms loss_block8
end Erdos7SupportPrefixChecks
