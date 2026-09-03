import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 28672 through 29695. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check28 : ∀ i : Fin 1024, ContainsCycle (28672 + i.val) := by decide +kernel
#print axioms check28
end Erdos184Work.PetersenBase
