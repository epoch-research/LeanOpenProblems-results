import Submission.PureFiveFilter4
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false
lemma prototype_complete : ∀ j : Fin 1000, Compatible j.val →
    (table.lookup j.val).isSome = true := by decide +kernel
#print axioms prototype_complete
end Erdos184Work.PureFiveFilter4
