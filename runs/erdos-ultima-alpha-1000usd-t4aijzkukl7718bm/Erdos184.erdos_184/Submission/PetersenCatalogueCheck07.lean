import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 7168 through 8191. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check7 : ∀ i : Fin 1024, ContainsCycle (7168 + i.val) := by decide +kernel
#print axioms check7
end Erdos184Work.PetersenBase
