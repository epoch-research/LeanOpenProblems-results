import Submission.PetersenCatalogueChecks

/-! Petersen support-catalogue check on masks 6144 through 7167. -/
namespace Erdos184Work.PetersenBase
set_option maxHeartbeats 50000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma check6 : ∀ i : Fin 1024, ContainsCycle (6144 + i.val) := by decide +kernel
#print axioms check6
end Erdos184Work.PetersenBase
