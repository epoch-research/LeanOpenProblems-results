import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1540 : ∀ i : Fin 200, Compatible (308000 + i.val) →
    (table.lookup (308000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1540 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 308000 308200 :=
  FiniteIntervals.of_fin 308000 200 complete_chunk1540

lemma complete_chunk1541 : ∀ i : Fin 200, Compatible (308200 + i.val) →
    (table.lookup (308200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1541 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 308200 308400 :=
  FiniteIntervals.of_fin 308200 200 complete_chunk1541

lemma complete_chunk1542 : ∀ i : Fin 200, Compatible (308400 + i.val) →
    (table.lookup (308400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1542 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 308400 308600 :=
  FiniteIntervals.of_fin 308400 200 complete_chunk1542

lemma complete_chunk1543 : ∀ i : Fin 200, Compatible (308600 + i.val) →
    (table.lookup (308600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1543 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 308600 308800 :=
  FiniteIntervals.of_fin 308600 200 complete_chunk1543

lemma complete_chunk1544 : ∀ i : Fin 200, Compatible (308800 + i.val) →
    (table.lookup (308800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1544 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 308800 309000 :=
  FiniteIntervals.of_fin 308800 200 complete_chunk1544

lemma complete_chunk1545 : ∀ i : Fin 200, Compatible (309000 + i.val) →
    (table.lookup (309000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1545 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 309000 309200 :=
  FiniteIntervals.of_fin 309000 200 complete_chunk1545

lemma complete_chunk1546 : ∀ i : Fin 200, Compatible (309200 + i.val) →
    (table.lookup (309200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1546 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 309200 309400 :=
  FiniteIntervals.of_fin 309200 200 complete_chunk1546

lemma complete_chunk1547 : ∀ i : Fin 200, Compatible (309400 + i.val) →
    (table.lookup (309400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1547 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 309400 309600 :=
  FiniteIntervals.of_fin 309400 200 complete_chunk1547

lemma complete_chunk1548 : ∀ i : Fin 200, Compatible (309600 + i.val) →
    (table.lookup (309600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1548 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 309600 309800 :=
  FiniteIntervals.of_fin 309600 200 complete_chunk1548

lemma complete_chunk1549 : ∀ i : Fin 200, Compatible (309800 + i.val) →
    (table.lookup (309800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1549 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 309800 310000 :=
  FiniteIntervals.of_fin 309800 200 complete_chunk1549

#print axioms interval_chunk1540
end Erdos184Work.PureFiveFilter4
