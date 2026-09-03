import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2760 : ∀ i : Fin 200, Compatible (552000 + i.val) →
    (table.lookup (552000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2760 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 552000 552200 :=
  FiniteIntervals.of_fin 552000 200 complete_chunk2760

lemma complete_chunk2761 : ∀ i : Fin 200, Compatible (552200 + i.val) →
    (table.lookup (552200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2761 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 552200 552400 :=
  FiniteIntervals.of_fin 552200 200 complete_chunk2761

lemma complete_chunk2762 : ∀ i : Fin 200, Compatible (552400 + i.val) →
    (table.lookup (552400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2762 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 552400 552600 :=
  FiniteIntervals.of_fin 552400 200 complete_chunk2762

lemma complete_chunk2763 : ∀ i : Fin 200, Compatible (552600 + i.val) →
    (table.lookup (552600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2763 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 552600 552800 :=
  FiniteIntervals.of_fin 552600 200 complete_chunk2763

lemma complete_chunk2764 : ∀ i : Fin 200, Compatible (552800 + i.val) →
    (table.lookup (552800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2764 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 552800 553000 :=
  FiniteIntervals.of_fin 552800 200 complete_chunk2764

lemma complete_chunk2765 : ∀ i : Fin 200, Compatible (553000 + i.val) →
    (table.lookup (553000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2765 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 553000 553200 :=
  FiniteIntervals.of_fin 553000 200 complete_chunk2765

lemma complete_chunk2766 : ∀ i : Fin 200, Compatible (553200 + i.val) →
    (table.lookup (553200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2766 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 553200 553400 :=
  FiniteIntervals.of_fin 553200 200 complete_chunk2766

lemma complete_chunk2767 : ∀ i : Fin 200, Compatible (553400 + i.val) →
    (table.lookup (553400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2767 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 553400 553600 :=
  FiniteIntervals.of_fin 553400 200 complete_chunk2767

lemma complete_chunk2768 : ∀ i : Fin 200, Compatible (553600 + i.val) →
    (table.lookup (553600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2768 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 553600 553800 :=
  FiniteIntervals.of_fin 553600 200 complete_chunk2768

lemma complete_chunk2769 : ∀ i : Fin 200, Compatible (553800 + i.val) →
    (table.lookup (553800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2769 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 553800 554000 :=
  FiniteIntervals.of_fin 553800 200 complete_chunk2769

#print axioms interval_chunk2760
end Erdos184Work.PureFiveFilter4
