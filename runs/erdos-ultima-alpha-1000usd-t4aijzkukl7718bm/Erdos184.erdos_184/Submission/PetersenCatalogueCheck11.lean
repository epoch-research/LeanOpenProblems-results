import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 11264 through 12287. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check11 : ∀ i : Fin 1024, ContainsCycle (11264 + i.val) := by decide +kernel
#print axioms check11
end Erdos184Work.PetersenBase
