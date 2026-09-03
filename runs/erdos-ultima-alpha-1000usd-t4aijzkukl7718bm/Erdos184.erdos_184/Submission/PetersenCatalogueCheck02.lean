import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 2048 through 3071. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check2 : ∀ i : Fin 1024, ContainsCycle (2048 + i.val) := by decide +kernel
#print axioms check2
end Erdos184Work.PetersenBase
