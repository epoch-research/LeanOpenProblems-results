import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 23552 through 24575. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check23 : ∀ i : Fin 1024, ContainsCycle (23552 + i.val) := by decide +kernel
#print axioms check23
end Erdos184Work.PetersenBase
