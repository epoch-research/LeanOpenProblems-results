import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6090 : ∀ i : Fin 200, Compatible (1218000 + i.val) →
    (table.lookup (1218000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6090 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1218000 1218200 :=
  FiniteIntervals.of_fin 1218000 200 complete_chunk6090

lemma complete_chunk6091 : ∀ i : Fin 200, Compatible (1218200 + i.val) →
    (table.lookup (1218200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6091 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1218200 1218400 :=
  FiniteIntervals.of_fin 1218200 200 complete_chunk6091

lemma complete_chunk6092 : ∀ i : Fin 200, Compatible (1218400 + i.val) →
    (table.lookup (1218400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6092 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1218400 1218600 :=
  FiniteIntervals.of_fin 1218400 200 complete_chunk6092

lemma complete_chunk6093 : ∀ i : Fin 200, Compatible (1218600 + i.val) →
    (table.lookup (1218600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6093 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1218600 1218800 :=
  FiniteIntervals.of_fin 1218600 200 complete_chunk6093

lemma complete_chunk6094 : ∀ i : Fin 200, Compatible (1218800 + i.val) →
    (table.lookup (1218800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6094 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1218800 1219000 :=
  FiniteIntervals.of_fin 1218800 200 complete_chunk6094

lemma complete_chunk6095 : ∀ i : Fin 200, Compatible (1219000 + i.val) →
    (table.lookup (1219000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6095 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1219000 1219200 :=
  FiniteIntervals.of_fin 1219000 200 complete_chunk6095

lemma complete_chunk6096 : ∀ i : Fin 200, Compatible (1219200 + i.val) →
    (table.lookup (1219200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6096 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1219200 1219400 :=
  FiniteIntervals.of_fin 1219200 200 complete_chunk6096

lemma complete_chunk6097 : ∀ i : Fin 200, Compatible (1219400 + i.val) →
    (table.lookup (1219400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6097 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1219400 1219600 :=
  FiniteIntervals.of_fin 1219400 200 complete_chunk6097

lemma complete_chunk6098 : ∀ i : Fin 200, Compatible (1219600 + i.val) →
    (table.lookup (1219600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6098 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1219600 1219800 :=
  FiniteIntervals.of_fin 1219600 200 complete_chunk6098

lemma complete_chunk6099 : ∀ i : Fin 200, Compatible (1219800 + i.val) →
    (table.lookup (1219800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6099 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1219800 1220000 :=
  FiniteIntervals.of_fin 1219800 200 complete_chunk6099

#print axioms interval_chunk6090
end Erdos184Work.PureFiveFilter4
