import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 29696 through 30719. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check29 : ∀ i : Fin 1024, ContainsCycle (29696 + i.val) := by decide +kernel
#print axioms check29
end Erdos184Work.PetersenBase
