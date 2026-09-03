import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 12288 through 13311. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check12 : ∀ i : Fin 1024, ContainsCycle (12288 + i.val) := by decide +kernel
#print axioms check12
end Erdos184Work.PetersenBase
