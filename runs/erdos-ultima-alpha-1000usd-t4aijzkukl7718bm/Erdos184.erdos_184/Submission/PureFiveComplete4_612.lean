import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6120 : ∀ i : Fin 200, Compatible (1224000 + i.val) →
    (table.lookup (1224000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1224000 1224200 :=
  FiniteIntervals.of_fin 1224000 200 complete_chunk6120

lemma complete_chunk6121 : ∀ i : Fin 200, Compatible (1224200 + i.val) →
    (table.lookup (1224200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1224200 1224400 :=
  FiniteIntervals.of_fin 1224200 200 complete_chunk6121

lemma complete_chunk6122 : ∀ i : Fin 200, Compatible (1224400 + i.val) →
    (table.lookup (1224400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1224400 1224600 :=
  FiniteIntervals.of_fin 1224400 200 complete_chunk6122

lemma complete_chunk6123 : ∀ i : Fin 200, Compatible (1224600 + i.val) →
    (table.lookup (1224600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1224600 1224800 :=
  FiniteIntervals.of_fin 1224600 200 complete_chunk6123

lemma complete_chunk6124 : ∀ i : Fin 200, Compatible (1224800 + i.val) →
    (table.lookup (1224800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1224800 1225000 :=
  FiniteIntervals.of_fin 1224800 200 complete_chunk6124

lemma complete_chunk6125 : ∀ i : Fin 200, Compatible (1225000 + i.val) →
    (table.lookup (1225000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1225000 1225200 :=
  FiniteIntervals.of_fin 1225000 200 complete_chunk6125

lemma complete_chunk6126 : ∀ i : Fin 200, Compatible (1225200 + i.val) →
    (table.lookup (1225200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1225200 1225400 :=
  FiniteIntervals.of_fin 1225200 200 complete_chunk6126

lemma complete_chunk6127 : ∀ i : Fin 200, Compatible (1225400 + i.val) →
    (table.lookup (1225400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1225400 1225600 :=
  FiniteIntervals.of_fin 1225400 200 complete_chunk6127

lemma complete_chunk6128 : ∀ i : Fin 200, Compatible (1225600 + i.val) →
    (table.lookup (1225600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1225600 1225800 :=
  FiniteIntervals.of_fin 1225600 200 complete_chunk6128

lemma complete_chunk6129 : ∀ i : Fin 200, Compatible (1225800 + i.val) →
    (table.lookup (1225800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1225800 1226000 :=
  FiniteIntervals.of_fin 1225800 200 complete_chunk6129

#print axioms interval_chunk6120
end Erdos184Work.PureFiveFilter4
