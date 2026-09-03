import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 8192 through 9215. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check8 : ∀ i : Fin 1024, ContainsCycle (8192 + i.val) := by decide +kernel
#print axioms check8
end Erdos184Work.PetersenBase
