import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1030 : ∀ i : Fin 200, Compatible (206000 + i.val) →
    (table.lookup (206000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1030 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 206000 206200 :=
  FiniteIntervals.of_fin 206000 200 complete_chunk1030

lemma complete_chunk1031 : ∀ i : Fin 200, Compatible (206200 + i.val) →
    (table.lookup (206200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1031 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 206200 206400 :=
  FiniteIntervals.of_fin 206200 200 complete_chunk1031

lemma complete_chunk1032 : ∀ i : Fin 200, Compatible (206400 + i.val) →
    (table.lookup (206400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1032 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 206400 206600 :=
  FiniteIntervals.of_fin 206400 200 complete_chunk1032

lemma complete_chunk1033 : ∀ i : Fin 200, Compatible (206600 + i.val) →
    (table.lookup (206600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1033 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 206600 206800 :=
  FiniteIntervals.of_fin 206600 200 complete_chunk1033

lemma complete_chunk1034 : ∀ i : Fin 200, Compatible (206800 + i.val) →
    (table.lookup (206800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1034 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 206800 207000 :=
  FiniteIntervals.of_fin 206800 200 complete_chunk1034

lemma complete_chunk1035 : ∀ i : Fin 200, Compatible (207000 + i.val) →
    (table.lookup (207000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1035 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 207000 207200 :=
  FiniteIntervals.of_fin 207000 200 complete_chunk1035

lemma complete_chunk1036 : ∀ i : Fin 200, Compatible (207200 + i.val) →
    (table.lookup (207200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1036 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 207200 207400 :=
  FiniteIntervals.of_fin 207200 200 complete_chunk1036

lemma complete_chunk1037 : ∀ i : Fin 200, Compatible (207400 + i.val) →
    (table.lookup (207400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1037 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 207400 207600 :=
  FiniteIntervals.of_fin 207400 200 complete_chunk1037

lemma complete_chunk1038 : ∀ i : Fin 200, Compatible (207600 + i.val) →
    (table.lookup (207600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1038 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 207600 207800 :=
  FiniteIntervals.of_fin 207600 200 complete_chunk1038

lemma complete_chunk1039 : ∀ i : Fin 200, Compatible (207800 + i.val) →
    (table.lookup (207800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1039 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 207800 208000 :=
  FiniteIntervals.of_fin 207800 200 complete_chunk1039

#print axioms interval_chunk1030
end Erdos184Work.PureFiveFilter4
