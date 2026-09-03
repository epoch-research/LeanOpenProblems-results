import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 25600 through 26623. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check25 : ∀ i : Fin 1024, ContainsCycle (25600 + i.val) := by decide +kernel
#print axioms check25
end Erdos184Work.PetersenBase
