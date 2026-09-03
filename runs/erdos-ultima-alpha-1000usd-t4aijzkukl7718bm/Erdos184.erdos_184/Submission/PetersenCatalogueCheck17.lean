import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 17408 through 18431. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check17 : ∀ i : Fin 1024, ContainsCycle (17408 + i.val) := by decide +kernel
#print axioms check17
end Erdos184Work.PetersenBase
