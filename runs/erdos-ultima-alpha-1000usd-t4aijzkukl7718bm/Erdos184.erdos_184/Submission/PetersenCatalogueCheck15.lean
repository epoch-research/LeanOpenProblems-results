import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 15360 through 16383. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check15 : ∀ i : Fin 1024, ContainsCycle (15360 + i.val) := by decide +kernel
#print axioms check15
end Erdos184Work.PetersenBase
