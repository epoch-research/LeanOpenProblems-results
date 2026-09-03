import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 24576 through 25599. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check24 : ∀ i : Fin 1024, ContainsCycle (24576 + i.val) := by decide +kernel
#print axioms check24
end Erdos184Work.PetersenBase
