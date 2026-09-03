import Submission.SupportPrefixCheckDefs
/-! Kernel-checked integer rows for an auxiliary prefix certificate. -/
namespace Erdos7SupportPrefixChecks
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem lower_block12 : ∀ i : Fin 4, ∀ j : Fin 180, lowerRow (i.val+48) j := by decide +kernel
theorem moment_block12 : ∀ i : Fin 4, ∀ j : Fin 10, momentRow (i.val+48) j := by decide +kernel
theorem loss_block12 : ∀ i : Fin 4, lossRow (i.val+48) := by decide +kernel
#print axioms lower_block12
#print axioms moment_block12
#print axioms loss_block12
end Erdos7SupportPrefixChecks
