import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6030 : ∀ i : Fin 200, Compatible (1206000 + i.val) →
    (table.lookup (1206000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6030 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1206000 1206200 :=
  FiniteIntervals.of_fin 1206000 200 complete_chunk6030

lemma complete_chunk6031 : ∀ i : Fin 200, Compatible (1206200 + i.val) →
    (table.lookup (1206200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6031 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1206200 1206400 :=
  FiniteIntervals.of_fin 1206200 200 complete_chunk6031

lemma complete_chunk6032 : ∀ i : Fin 200, Compatible (1206400 + i.val) →
    (table.lookup (1206400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6032 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1206400 1206600 :=
  FiniteIntervals.of_fin 1206400 200 complete_chunk6032

lemma complete_chunk6033 : ∀ i : Fin 200, Compatible (1206600 + i.val) →
    (table.lookup (1206600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6033 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1206600 1206800 :=
  FiniteIntervals.of_fin 1206600 200 complete_chunk6033

lemma complete_chunk6034 : ∀ i : Fin 200, Compatible (1206800 + i.val) →
    (table.lookup (1206800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6034 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1206800 1207000 :=
  FiniteIntervals.of_fin 1206800 200 complete_chunk6034

lemma complete_chunk6035 : ∀ i : Fin 200, Compatible (1207000 + i.val) →
    (table.lookup (1207000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6035 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1207000 1207200 :=
  FiniteIntervals.of_fin 1207000 200 complete_chunk6035

lemma complete_chunk6036 : ∀ i : Fin 200, Compatible (1207200 + i.val) →
    (table.lookup (1207200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6036 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1207200 1207400 :=
  FiniteIntervals.of_fin 1207200 200 complete_chunk6036

lemma complete_chunk6037 : ∀ i : Fin 200, Compatible (1207400 + i.val) →
    (table.lookup (1207400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6037 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1207400 1207600 :=
  FiniteIntervals.of_fin 1207400 200 complete_chunk6037

lemma complete_chunk6038 : ∀ i : Fin 200, Compatible (1207600 + i.val) →
    (table.lookup (1207600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6038 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1207600 1207800 :=
  FiniteIntervals.of_fin 1207600 200 complete_chunk6038

lemma complete_chunk6039 : ∀ i : Fin 200, Compatible (1207800 + i.val) →
    (table.lookup (1207800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6039 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1207800 1208000 :=
  FiniteIntervals.of_fin 1207800 200 complete_chunk6039

#print axioms interval_chunk6030
end Erdos184Work.PureFiveFilter4
