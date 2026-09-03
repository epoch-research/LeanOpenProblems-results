import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 14336 through 15359. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check14 : ∀ i : Fin 1024, ContainsCycle (14336 + i.val) := by decide +kernel
#print axioms check14
end Erdos184Work.PetersenBase
