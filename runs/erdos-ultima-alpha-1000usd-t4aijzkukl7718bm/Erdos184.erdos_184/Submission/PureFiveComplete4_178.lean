import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1780 : ∀ i : Fin 200, Compatible (356000 + i.val) →
    (table.lookup (356000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1780 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 356000 356200 :=
  FiniteIntervals.of_fin 356000 200 complete_chunk1780

lemma complete_chunk1781 : ∀ i : Fin 200, Compatible (356200 + i.val) →
    (table.lookup (356200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1781 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 356200 356400 :=
  FiniteIntervals.of_fin 356200 200 complete_chunk1781

lemma complete_chunk1782 : ∀ i : Fin 200, Compatible (356400 + i.val) →
    (table.lookup (356400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1782 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 356400 356600 :=
  FiniteIntervals.of_fin 356400 200 complete_chunk1782

lemma complete_chunk1783 : ∀ i : Fin 200, Compatible (356600 + i.val) →
    (table.lookup (356600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1783 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 356600 356800 :=
  FiniteIntervals.of_fin 356600 200 complete_chunk1783

lemma complete_chunk1784 : ∀ i : Fin 200, Compatible (356800 + i.val) →
    (table.lookup (356800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1784 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 356800 357000 :=
  FiniteIntervals.of_fin 356800 200 complete_chunk1784

lemma complete_chunk1785 : ∀ i : Fin 200, Compatible (357000 + i.val) →
    (table.lookup (357000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1785 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 357000 357200 :=
  FiniteIntervals.of_fin 357000 200 complete_chunk1785

lemma complete_chunk1786 : ∀ i : Fin 200, Compatible (357200 + i.val) →
    (table.lookup (357200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1786 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 357200 357400 :=
  FiniteIntervals.of_fin 357200 200 complete_chunk1786

lemma complete_chunk1787 : ∀ i : Fin 200, Compatible (357400 + i.val) →
    (table.lookup (357400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1787 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 357400 357600 :=
  FiniteIntervals.of_fin 357400 200 complete_chunk1787

lemma complete_chunk1788 : ∀ i : Fin 200, Compatible (357600 + i.val) →
    (table.lookup (357600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1788 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 357600 357800 :=
  FiniteIntervals.of_fin 357600 200 complete_chunk1788

lemma complete_chunk1789 : ∀ i : Fin 200, Compatible (357800 + i.val) →
    (table.lookup (357800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1789 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 357800 358000 :=
  FiniteIntervals.of_fin 357800 200 complete_chunk1789

#print axioms interval_chunk1780
end Erdos184Work.PureFiveFilter4
