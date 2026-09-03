import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 19456 through 20479. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check19 : ∀ i : Fin 1024, ContainsCycle (19456 + i.val) := by decide +kernel
#print axioms check19
end Erdos184Work.PetersenBase
