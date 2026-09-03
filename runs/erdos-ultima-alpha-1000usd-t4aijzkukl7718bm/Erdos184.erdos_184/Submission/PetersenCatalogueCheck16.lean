import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 16384 through 17407. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check16 : ∀ i : Fin 1024, ContainsCycle (16384 + i.val) := by decide +kernel
#print axioms check16
end Erdos184Work.PetersenBase
