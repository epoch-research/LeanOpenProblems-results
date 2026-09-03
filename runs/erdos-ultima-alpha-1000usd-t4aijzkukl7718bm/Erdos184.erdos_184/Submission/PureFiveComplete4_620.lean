import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6200 : ∀ i : Fin 200, Compatible (1240000 + i.val) →
    (table.lookup (1240000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1240000 1240200 :=
  FiniteIntervals.of_fin 1240000 200 complete_chunk6200

lemma complete_chunk6201 : ∀ i : Fin 200, Compatible (1240200 + i.val) →
    (table.lookup (1240200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1240200 1240400 :=
  FiniteIntervals.of_fin 1240200 200 complete_chunk6201

lemma complete_chunk6202 : ∀ i : Fin 200, Compatible (1240400 + i.val) →
    (table.lookup (1240400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1240400 1240600 :=
  FiniteIntervals.of_fin 1240400 200 complete_chunk6202

lemma complete_chunk6203 : ∀ i : Fin 200, Compatible (1240600 + i.val) →
    (table.lookup (1240600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1240600 1240800 :=
  FiniteIntervals.of_fin 1240600 200 complete_chunk6203

lemma complete_chunk6204 : ∀ i : Fin 200, Compatible (1240800 + i.val) →
    (table.lookup (1240800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1240800 1241000 :=
  FiniteIntervals.of_fin 1240800 200 complete_chunk6204

lemma complete_chunk6205 : ∀ i : Fin 200, Compatible (1241000 + i.val) →
    (table.lookup (1241000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1241000 1241200 :=
  FiniteIntervals.of_fin 1241000 200 complete_chunk6205

lemma complete_chunk6206 : ∀ i : Fin 200, Compatible (1241200 + i.val) →
    (table.lookup (1241200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1241200 1241400 :=
  FiniteIntervals.of_fin 1241200 200 complete_chunk6206

lemma complete_chunk6207 : ∀ i : Fin 200, Compatible (1241400 + i.val) →
    (table.lookup (1241400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1241400 1241600 :=
  FiniteIntervals.of_fin 1241400 200 complete_chunk6207

lemma complete_chunk6208 : ∀ i : Fin 200, Compatible (1241600 + i.val) →
    (table.lookup (1241600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1241600 1241800 :=
  FiniteIntervals.of_fin 1241600 200 complete_chunk6208

lemma complete_chunk6209 : ∀ i : Fin 200, Compatible (1241800 + i.val) →
    (table.lookup (1241800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1241800 1242000 :=
  FiniteIntervals.of_fin 1241800 200 complete_chunk6209

#print axioms interval_chunk6200
end Erdos184Work.PureFiveFilter4
