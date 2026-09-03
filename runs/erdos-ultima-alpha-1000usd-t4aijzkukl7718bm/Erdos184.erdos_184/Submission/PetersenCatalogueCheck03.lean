import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 3072 through 4095. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check3 : ∀ i : Fin 1024, ContainsCycle (3072 + i.val) := by decide +kernel
#print axioms check3
end Erdos184Work.PetersenBase
