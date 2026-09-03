import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 10240 through 11263. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check10 : ∀ i : Fin 1024, ContainsCycle (10240 + i.val) := by decide +kernel
#print axioms check10
end Erdos184Work.PetersenBase
