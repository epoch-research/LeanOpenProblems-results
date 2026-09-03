import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1090 : ∀ i : Fin 200, Compatible (218000 + i.val) →
    (table.lookup (218000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1090 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 218000 218200 :=
  FiniteIntervals.of_fin 218000 200 complete_chunk1090

lemma complete_chunk1091 : ∀ i : Fin 200, Compatible (218200 + i.val) →
    (table.lookup (218200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1091 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 218200 218400 :=
  FiniteIntervals.of_fin 218200 200 complete_chunk1091

lemma complete_chunk1092 : ∀ i : Fin 200, Compatible (218400 + i.val) →
    (table.lookup (218400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1092 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 218400 218600 :=
  FiniteIntervals.of_fin 218400 200 complete_chunk1092

lemma complete_chunk1093 : ∀ i : Fin 200, Compatible (218600 + i.val) →
    (table.lookup (218600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1093 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 218600 218800 :=
  FiniteIntervals.of_fin 218600 200 complete_chunk1093

lemma complete_chunk1094 : ∀ i : Fin 200, Compatible (218800 + i.val) →
    (table.lookup (218800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1094 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 218800 219000 :=
  FiniteIntervals.of_fin 218800 200 complete_chunk1094

lemma complete_chunk1095 : ∀ i : Fin 200, Compatible (219000 + i.val) →
    (table.lookup (219000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1095 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 219000 219200 :=
  FiniteIntervals.of_fin 219000 200 complete_chunk1095

lemma complete_chunk1096 : ∀ i : Fin 200, Compatible (219200 + i.val) →
    (table.lookup (219200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1096 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 219200 219400 :=
  FiniteIntervals.of_fin 219200 200 complete_chunk1096

lemma complete_chunk1097 : ∀ i : Fin 200, Compatible (219400 + i.val) →
    (table.lookup (219400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1097 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 219400 219600 :=
  FiniteIntervals.of_fin 219400 200 complete_chunk1097

lemma complete_chunk1098 : ∀ i : Fin 200, Compatible (219600 + i.val) →
    (table.lookup (219600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1098 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 219600 219800 :=
  FiniteIntervals.of_fin 219600 200 complete_chunk1098

lemma complete_chunk1099 : ∀ i : Fin 200, Compatible (219800 + i.val) →
    (table.lookup (219800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1099 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 219800 220000 :=
  FiniteIntervals.of_fin 219800 200 complete_chunk1099

#print axioms interval_chunk1090
end Erdos184Work.PureFiveFilter4
