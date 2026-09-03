import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1560 : ∀ i : Fin 200, Compatible (312000 + i.val) →
    (table.lookup (312000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1560 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 312000 312200 :=
  FiniteIntervals.of_fin 312000 200 complete_chunk1560

lemma complete_chunk1561 : ∀ i : Fin 200, Compatible (312200 + i.val) →
    (table.lookup (312200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1561 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 312200 312400 :=
  FiniteIntervals.of_fin 312200 200 complete_chunk1561

lemma complete_chunk1562 : ∀ i : Fin 200, Compatible (312400 + i.val) →
    (table.lookup (312400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1562 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 312400 312600 :=
  FiniteIntervals.of_fin 312400 200 complete_chunk1562

lemma complete_chunk1563 : ∀ i : Fin 200, Compatible (312600 + i.val) →
    (table.lookup (312600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1563 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 312600 312800 :=
  FiniteIntervals.of_fin 312600 200 complete_chunk1563

lemma complete_chunk1564 : ∀ i : Fin 200, Compatible (312800 + i.val) →
    (table.lookup (312800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1564 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 312800 313000 :=
  FiniteIntervals.of_fin 312800 200 complete_chunk1564

lemma complete_chunk1565 : ∀ i : Fin 200, Compatible (313000 + i.val) →
    (table.lookup (313000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1565 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 313000 313200 :=
  FiniteIntervals.of_fin 313000 200 complete_chunk1565

lemma complete_chunk1566 : ∀ i : Fin 200, Compatible (313200 + i.val) →
    (table.lookup (313200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1566 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 313200 313400 :=
  FiniteIntervals.of_fin 313200 200 complete_chunk1566

lemma complete_chunk1567 : ∀ i : Fin 200, Compatible (313400 + i.val) →
    (table.lookup (313400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1567 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 313400 313600 :=
  FiniteIntervals.of_fin 313400 200 complete_chunk1567

lemma complete_chunk1568 : ∀ i : Fin 200, Compatible (313600 + i.val) →
    (table.lookup (313600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1568 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 313600 313800 :=
  FiniteIntervals.of_fin 313600 200 complete_chunk1568

lemma complete_chunk1569 : ∀ i : Fin 200, Compatible (313800 + i.val) →
    (table.lookup (313800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1569 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 313800 314000 :=
  FiniteIntervals.of_fin 313800 200 complete_chunk1569

#print axioms interval_chunk1560
end Erdos184Work.PureFiveFilter4
