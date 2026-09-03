import Submission.SupportPrefixCheckDefs
/-! Kernel-checked integer rows for an auxiliary prefix certificate. -/
namespace Erdos7SupportPrefixChecks
set_option maxHeartbeats 0
set_option maxRecDepth 200000
set_option Elab.async false
theorem lower_block6 : ∀ i : Fin 4, ∀ j : Fin 180, lowerRow (i.val+24) j := by decide +kernel
theorem moment_block6 : ∀ i : Fin 4, ∀ j : Fin 10, momentRow (i.val+24) j := by decide +kernel
theorem loss_block6 : ∀ i : Fin 4, lossRow (i.val+24) := by decide +kernel
#print axioms lower_block6
#print axioms moment_block6
#print axioms loss_block6
end Erdos7SupportPrefixChecks
