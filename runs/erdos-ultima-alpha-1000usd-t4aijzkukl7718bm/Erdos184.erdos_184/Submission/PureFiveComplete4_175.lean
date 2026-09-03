import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1750 : ∀ i : Fin 200, Compatible (350000 + i.val) →
    (table.lookup (350000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1750 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 350000 350200 :=
  FiniteIntervals.of_fin 350000 200 complete_chunk1750

lemma complete_chunk1751 : ∀ i : Fin 200, Compatible (350200 + i.val) →
    (table.lookup (350200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1751 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 350200 350400 :=
  FiniteIntervals.of_fin 350200 200 complete_chunk1751

lemma complete_chunk1752 : ∀ i : Fin 200, Compatible (350400 + i.val) →
    (table.lookup (350400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1752 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 350400 350600 :=
  FiniteIntervals.of_fin 350400 200 complete_chunk1752

lemma complete_chunk1753 : ∀ i : Fin 200, Compatible (350600 + i.val) →
    (table.lookup (350600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1753 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 350600 350800 :=
  FiniteIntervals.of_fin 350600 200 complete_chunk1753

lemma complete_chunk1754 : ∀ i : Fin 200, Compatible (350800 + i.val) →
    (table.lookup (350800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1754 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 350800 351000 :=
  FiniteIntervals.of_fin 350800 200 complete_chunk1754

lemma complete_chunk1755 : ∀ i : Fin 200, Compatible (351000 + i.val) →
    (table.lookup (351000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1755 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 351000 351200 :=
  FiniteIntervals.of_fin 351000 200 complete_chunk1755

lemma complete_chunk1756 : ∀ i : Fin 200, Compatible (351200 + i.val) →
    (table.lookup (351200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1756 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 351200 351400 :=
  FiniteIntervals.of_fin 351200 200 complete_chunk1756

lemma complete_chunk1757 : ∀ i : Fin 200, Compatible (351400 + i.val) →
    (table.lookup (351400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1757 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 351400 351600 :=
  FiniteIntervals.of_fin 351400 200 complete_chunk1757

lemma complete_chunk1758 : ∀ i : Fin 200, Compatible (351600 + i.val) →
    (table.lookup (351600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1758 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 351600 351800 :=
  FiniteIntervals.of_fin 351600 200 complete_chunk1758

lemma complete_chunk1759 : ∀ i : Fin 200, Compatible (351800 + i.val) →
    (table.lookup (351800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1759 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 351800 352000 :=
  FiniteIntervals.of_fin 351800 200 complete_chunk1759

#print axioms interval_chunk1750
end Erdos184Work.PureFiveFilter4
