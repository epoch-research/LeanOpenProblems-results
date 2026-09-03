import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 9216 through 10239. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check9 : ∀ i : Fin 1024, ContainsCycle (9216 + i.val) := by decide +kernel
#print axioms check9
end Erdos184Work.PetersenBase
