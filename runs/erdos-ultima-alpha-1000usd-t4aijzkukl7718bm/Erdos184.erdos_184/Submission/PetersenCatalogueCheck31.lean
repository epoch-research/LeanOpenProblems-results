import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 31744 through 32767. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check31 : ∀ i : Fin 1024, ContainsCycle (31744 + i.val) := by decide +kernel
#print axioms check31
end Erdos184Work.PetersenBase
