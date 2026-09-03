import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4670 : ∀ i : Fin 200, Compatible (934000 + i.val) →
    (table.lookup (934000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4670 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 934000 934200 :=
  FiniteIntervals.of_fin 934000 200 complete_chunk4670

lemma complete_chunk4671 : ∀ i : Fin 200, Compatible (934200 + i.val) →
    (table.lookup (934200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4671 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 934200 934400 :=
  FiniteIntervals.of_fin 934200 200 complete_chunk4671

lemma complete_chunk4672 : ∀ i : Fin 200, Compatible (934400 + i.val) →
    (table.lookup (934400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4672 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 934400 934600 :=
  FiniteIntervals.of_fin 934400 200 complete_chunk4672

lemma complete_chunk4673 : ∀ i : Fin 200, Compatible (934600 + i.val) →
    (table.lookup (934600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4673 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 934600 934800 :=
  FiniteIntervals.of_fin 934600 200 complete_chunk4673

lemma complete_chunk4674 : ∀ i : Fin 200, Compatible (934800 + i.val) →
    (table.lookup (934800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4674 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 934800 935000 :=
  FiniteIntervals.of_fin 934800 200 complete_chunk4674

lemma complete_chunk4675 : ∀ i : Fin 200, Compatible (935000 + i.val) →
    (table.lookup (935000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4675 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 935000 935200 :=
  FiniteIntervals.of_fin 935000 200 complete_chunk4675

lemma complete_chunk4676 : ∀ i : Fin 200, Compatible (935200 + i.val) →
    (table.lookup (935200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4676 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 935200 935400 :=
  FiniteIntervals.of_fin 935200 200 complete_chunk4676

lemma complete_chunk4677 : ∀ i : Fin 200, Compatible (935400 + i.val) →
    (table.lookup (935400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4677 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 935400 935600 :=
  FiniteIntervals.of_fin 935400 200 complete_chunk4677

lemma complete_chunk4678 : ∀ i : Fin 200, Compatible (935600 + i.val) →
    (table.lookup (935600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4678 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 935600 935800 :=
  FiniteIntervals.of_fin 935600 200 complete_chunk4678

lemma complete_chunk4679 : ∀ i : Fin 200, Compatible (935800 + i.val) →
    (table.lookup (935800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4679 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 935800 936000 :=
  FiniteIntervals.of_fin 935800 200 complete_chunk4679

#print axioms interval_chunk4670
end Erdos184Work.PureFiveFilter4
