import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6180 : ∀ i : Fin 200, Compatible (1236000 + i.val) →
    (table.lookup (1236000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1236000 1236200 :=
  FiniteIntervals.of_fin 1236000 200 complete_chunk6180

lemma complete_chunk6181 : ∀ i : Fin 200, Compatible (1236200 + i.val) →
    (table.lookup (1236200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1236200 1236400 :=
  FiniteIntervals.of_fin 1236200 200 complete_chunk6181

lemma complete_chunk6182 : ∀ i : Fin 200, Compatible (1236400 + i.val) →
    (table.lookup (1236400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1236400 1236600 :=
  FiniteIntervals.of_fin 1236400 200 complete_chunk6182

lemma complete_chunk6183 : ∀ i : Fin 200, Compatible (1236600 + i.val) →
    (table.lookup (1236600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1236600 1236800 :=
  FiniteIntervals.of_fin 1236600 200 complete_chunk6183

lemma complete_chunk6184 : ∀ i : Fin 200, Compatible (1236800 + i.val) →
    (table.lookup (1236800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1236800 1237000 :=
  FiniteIntervals.of_fin 1236800 200 complete_chunk6184

lemma complete_chunk6185 : ∀ i : Fin 200, Compatible (1237000 + i.val) →
    (table.lookup (1237000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1237000 1237200 :=
  FiniteIntervals.of_fin 1237000 200 complete_chunk6185

lemma complete_chunk6186 : ∀ i : Fin 200, Compatible (1237200 + i.val) →
    (table.lookup (1237200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1237200 1237400 :=
  FiniteIntervals.of_fin 1237200 200 complete_chunk6186

lemma complete_chunk6187 : ∀ i : Fin 200, Compatible (1237400 + i.val) →
    (table.lookup (1237400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1237400 1237600 :=
  FiniteIntervals.of_fin 1237400 200 complete_chunk6187

lemma complete_chunk6188 : ∀ i : Fin 200, Compatible (1237600 + i.val) →
    (table.lookup (1237600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1237600 1237800 :=
  FiniteIntervals.of_fin 1237600 200 complete_chunk6188

lemma complete_chunk6189 : ∀ i : Fin 200, Compatible (1237800 + i.val) →
    (table.lookup (1237800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1237800 1238000 :=
  FiniteIntervals.of_fin 1237800 200 complete_chunk6189

#print axioms interval_chunk6180
end Erdos184Work.PureFiveFilter4
