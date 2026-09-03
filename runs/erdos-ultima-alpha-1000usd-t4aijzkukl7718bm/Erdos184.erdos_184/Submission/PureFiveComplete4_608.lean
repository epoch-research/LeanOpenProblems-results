import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6080 : ∀ i : Fin 200, Compatible (1216000 + i.val) →
    (table.lookup (1216000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6080 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1216000 1216200 :=
  FiniteIntervals.of_fin 1216000 200 complete_chunk6080

lemma complete_chunk6081 : ∀ i : Fin 200, Compatible (1216200 + i.val) →
    (table.lookup (1216200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6081 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1216200 1216400 :=
  FiniteIntervals.of_fin 1216200 200 complete_chunk6081

lemma complete_chunk6082 : ∀ i : Fin 200, Compatible (1216400 + i.val) →
    (table.lookup (1216400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6082 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1216400 1216600 :=
  FiniteIntervals.of_fin 1216400 200 complete_chunk6082

lemma complete_chunk6083 : ∀ i : Fin 200, Compatible (1216600 + i.val) →
    (table.lookup (1216600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6083 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1216600 1216800 :=
  FiniteIntervals.of_fin 1216600 200 complete_chunk6083

lemma complete_chunk6084 : ∀ i : Fin 200, Compatible (1216800 + i.val) →
    (table.lookup (1216800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6084 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1216800 1217000 :=
  FiniteIntervals.of_fin 1216800 200 complete_chunk6084

lemma complete_chunk6085 : ∀ i : Fin 200, Compatible (1217000 + i.val) →
    (table.lookup (1217000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6085 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1217000 1217200 :=
  FiniteIntervals.of_fin 1217000 200 complete_chunk6085

lemma complete_chunk6086 : ∀ i : Fin 200, Compatible (1217200 + i.val) →
    (table.lookup (1217200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6086 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1217200 1217400 :=
  FiniteIntervals.of_fin 1217200 200 complete_chunk6086

lemma complete_chunk6087 : ∀ i : Fin 200, Compatible (1217400 + i.val) →
    (table.lookup (1217400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6087 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1217400 1217600 :=
  FiniteIntervals.of_fin 1217400 200 complete_chunk6087

lemma complete_chunk6088 : ∀ i : Fin 200, Compatible (1217600 + i.val) →
    (table.lookup (1217600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6088 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1217600 1217800 :=
  FiniteIntervals.of_fin 1217600 200 complete_chunk6088

lemma complete_chunk6089 : ∀ i : Fin 200, Compatible (1217800 + i.val) →
    (table.lookup (1217800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6089 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1217800 1218000 :=
  FiniteIntervals.of_fin 1217800 200 complete_chunk6089

#print axioms interval_chunk6080
end Erdos184Work.PureFiveFilter4
