import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 21504 through 22527. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check21 : ∀ i : Fin 1024, ContainsCycle (21504 + i.val) := by decide +kernel
#print axioms check21
end Erdos184Work.PetersenBase
