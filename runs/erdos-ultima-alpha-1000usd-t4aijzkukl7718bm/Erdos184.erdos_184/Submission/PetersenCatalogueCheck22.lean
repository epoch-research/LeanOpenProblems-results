import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 22528 through 23551. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check22 : ∀ i : Fin 1024, ContainsCycle (22528 + i.val) := by decide +kernel
#print axioms check22
end Erdos184Work.PetersenBase
