import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6220 : ∀ i : Fin 160, Compatible (1244000 + i.val) →
    (table.lookup (1244000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1244000 1244160 :=
  FiniteIntervals.of_fin 1244000 160 complete_chunk6220

#print axioms interval_chunk6220
end Erdos184Work.PureFiveFilter4
