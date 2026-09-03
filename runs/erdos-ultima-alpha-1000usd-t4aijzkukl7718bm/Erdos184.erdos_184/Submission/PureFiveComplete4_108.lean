import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1080 : ∀ i : Fin 200, Compatible (216000 + i.val) →
    (table.lookup (216000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1080 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 216000 216200 :=
  FiniteIntervals.of_fin 216000 200 complete_chunk1080

lemma complete_chunk1081 : ∀ i : Fin 200, Compatible (216200 + i.val) →
    (table.lookup (216200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1081 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 216200 216400 :=
  FiniteIntervals.of_fin 216200 200 complete_chunk1081

lemma complete_chunk1082 : ∀ i : Fin 200, Compatible (216400 + i.val) →
    (table.lookup (216400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1082 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 216400 216600 :=
  FiniteIntervals.of_fin 216400 200 complete_chunk1082

lemma complete_chunk1083 : ∀ i : Fin 200, Compatible (216600 + i.val) →
    (table.lookup (216600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1083 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 216600 216800 :=
  FiniteIntervals.of_fin 216600 200 complete_chunk1083

lemma complete_chunk1084 : ∀ i : Fin 200, Compatible (216800 + i.val) →
    (table.lookup (216800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1084 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 216800 217000 :=
  FiniteIntervals.of_fin 216800 200 complete_chunk1084

lemma complete_chunk1085 : ∀ i : Fin 200, Compatible (217000 + i.val) →
    (table.lookup (217000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1085 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 217000 217200 :=
  FiniteIntervals.of_fin 217000 200 complete_chunk1085

lemma complete_chunk1086 : ∀ i : Fin 200, Compatible (217200 + i.val) →
    (table.lookup (217200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1086 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 217200 217400 :=
  FiniteIntervals.of_fin 217200 200 complete_chunk1086

lemma complete_chunk1087 : ∀ i : Fin 200, Compatible (217400 + i.val) →
    (table.lookup (217400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1087 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 217400 217600 :=
  FiniteIntervals.of_fin 217400 200 complete_chunk1087

lemma complete_chunk1088 : ∀ i : Fin 200, Compatible (217600 + i.val) →
    (table.lookup (217600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1088 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 217600 217800 :=
  FiniteIntervals.of_fin 217600 200 complete_chunk1088

lemma complete_chunk1089 : ∀ i : Fin 200, Compatible (217800 + i.val) →
    (table.lookup (217800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1089 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 217800 218000 :=
  FiniteIntervals.of_fin 217800 200 complete_chunk1089

#print axioms interval_chunk1080
end Erdos184Work.PureFiveFilter4
