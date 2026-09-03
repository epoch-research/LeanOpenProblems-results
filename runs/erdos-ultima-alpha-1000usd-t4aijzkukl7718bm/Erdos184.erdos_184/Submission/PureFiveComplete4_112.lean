import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1120 : ∀ i : Fin 200, Compatible (224000 + i.val) →
    (table.lookup (224000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 224000 224200 :=
  FiniteIntervals.of_fin 224000 200 complete_chunk1120

lemma complete_chunk1121 : ∀ i : Fin 200, Compatible (224200 + i.val) →
    (table.lookup (224200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 224200 224400 :=
  FiniteIntervals.of_fin 224200 200 complete_chunk1121

lemma complete_chunk1122 : ∀ i : Fin 200, Compatible (224400 + i.val) →
    (table.lookup (224400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 224400 224600 :=
  FiniteIntervals.of_fin 224400 200 complete_chunk1122

lemma complete_chunk1123 : ∀ i : Fin 200, Compatible (224600 + i.val) →
    (table.lookup (224600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 224600 224800 :=
  FiniteIntervals.of_fin 224600 200 complete_chunk1123

lemma complete_chunk1124 : ∀ i : Fin 200, Compatible (224800 + i.val) →
    (table.lookup (224800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 224800 225000 :=
  FiniteIntervals.of_fin 224800 200 complete_chunk1124

lemma complete_chunk1125 : ∀ i : Fin 200, Compatible (225000 + i.val) →
    (table.lookup (225000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 225000 225200 :=
  FiniteIntervals.of_fin 225000 200 complete_chunk1125

lemma complete_chunk1126 : ∀ i : Fin 200, Compatible (225200 + i.val) →
    (table.lookup (225200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 225200 225400 :=
  FiniteIntervals.of_fin 225200 200 complete_chunk1126

lemma complete_chunk1127 : ∀ i : Fin 200, Compatible (225400 + i.val) →
    (table.lookup (225400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 225400 225600 :=
  FiniteIntervals.of_fin 225400 200 complete_chunk1127

lemma complete_chunk1128 : ∀ i : Fin 200, Compatible (225600 + i.val) →
    (table.lookup (225600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 225600 225800 :=
  FiniteIntervals.of_fin 225600 200 complete_chunk1128

lemma complete_chunk1129 : ∀ i : Fin 200, Compatible (225800 + i.val) →
    (table.lookup (225800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 225800 226000 :=
  FiniteIntervals.of_fin 225800 200 complete_chunk1129

#print axioms interval_chunk1120
end Erdos184Work.PureFiveFilter4
