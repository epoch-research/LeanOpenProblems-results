import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 27648 through 28671. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check27 : ∀ i : Fin 1024, ContainsCycle (27648 + i.val) := by decide +kernel
#print axioms check27
end Erdos184Work.PetersenBase
