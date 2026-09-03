import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk310 : ∀ i : Fin 200, Compatible (62000 + i.val) →
    (table.lookup (62000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk310 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62000 62200 :=
  FiniteIntervals.of_fin 62000 200 complete_chunk310

lemma complete_chunk311 : ∀ i : Fin 8, Compatible (62200 + i.val) →
    (table.lookup (62200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk311 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 62200 62208 :=
  FiniteIntervals.of_fin 62200 8 complete_chunk311

#print axioms interval_chunk310
end Erdos184Work.PureFiveFilter3
