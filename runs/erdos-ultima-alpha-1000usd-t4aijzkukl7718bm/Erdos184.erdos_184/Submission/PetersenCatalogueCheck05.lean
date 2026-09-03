import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 5120 through 6143. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check5 : ∀ i : Fin 1024, ContainsCycle (5120 + i.val) := by decide +kernel
#print axioms check5
end Erdos184Work.PetersenBase
