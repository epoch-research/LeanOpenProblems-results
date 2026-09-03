import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 26624 through 27647. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check26 : ∀ i : Fin 1024, ContainsCycle (26624 + i.val) := by decide +kernel
#print axioms check26
end Erdos184Work.PetersenBase
