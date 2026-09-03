import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 1024 through 2047. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check1 : ∀ i : Fin 1024, ContainsCycle (1024 + i.val) := by decide +kernel
#print axioms check1
end Erdos184Work.PetersenBase
