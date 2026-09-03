import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 18432 through 19455. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check18 : ∀ i : Fin 1024, ContainsCycle (18432 + i.val) := by decide +kernel
#print axioms check18
end Erdos184Work.PetersenBase
