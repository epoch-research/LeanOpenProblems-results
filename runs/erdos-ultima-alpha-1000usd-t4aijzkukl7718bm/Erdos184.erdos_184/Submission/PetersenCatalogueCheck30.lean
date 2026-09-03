import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 30720 through 31743. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check30 : ∀ i : Fin 1024, ContainsCycle (30720 + i.val) := by decide +kernel
#print axioms check30
end Erdos184Work.PetersenBase
