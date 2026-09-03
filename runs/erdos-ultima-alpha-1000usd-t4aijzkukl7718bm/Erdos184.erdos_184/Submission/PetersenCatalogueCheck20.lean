import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 20480 through 21503. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check20 : ∀ i : Fin 1024, ContainsCycle (20480 + i.val) := by decide +kernel
#print axioms check20
end Erdos184Work.PetersenBase
