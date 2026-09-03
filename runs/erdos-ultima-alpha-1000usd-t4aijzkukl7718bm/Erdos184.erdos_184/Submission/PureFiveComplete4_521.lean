import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5210 : ∀ i : Fin 200, Compatible (1042000 + i.val) →
    (table.lookup (1042000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1042000 1042200 :=
  FiniteIntervals.of_fin 1042000 200 complete_chunk5210

lemma complete_chunk5211 : ∀ i : Fin 200, Compatible (1042200 + i.val) →
    (table.lookup (1042200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1042200 1042400 :=
  FiniteIntervals.of_fin 1042200 200 complete_chunk5211

lemma complete_chunk5212 : ∀ i : Fin 200, Compatible (1042400 + i.val) →
    (table.lookup (1042400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1042400 1042600 :=
  FiniteIntervals.of_fin 1042400 200 complete_chunk5212

lemma complete_chunk5213 : ∀ i : Fin 200, Compatible (1042600 + i.val) →
    (table.lookup (1042600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1042600 1042800 :=
  FiniteIntervals.of_fin 1042600 200 complete_chunk5213

lemma complete_chunk5214 : ∀ i : Fin 200, Compatible (1042800 + i.val) →
    (table.lookup (1042800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1042800 1043000 :=
  FiniteIntervals.of_fin 1042800 200 complete_chunk5214

lemma complete_chunk5215 : ∀ i : Fin 200, Compatible (1043000 + i.val) →
    (table.lookup (1043000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1043000 1043200 :=
  FiniteIntervals.of_fin 1043000 200 complete_chunk5215

lemma complete_chunk5216 : ∀ i : Fin 200, Compatible (1043200 + i.val) →
    (table.lookup (1043200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1043200 1043400 :=
  FiniteIntervals.of_fin 1043200 200 complete_chunk5216

lemma complete_chunk5217 : ∀ i : Fin 200, Compatible (1043400 + i.val) →
    (table.lookup (1043400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1043400 1043600 :=
  FiniteIntervals.of_fin 1043400 200 complete_chunk5217

lemma complete_chunk5218 : ∀ i : Fin 200, Compatible (1043600 + i.val) →
    (table.lookup (1043600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1043600 1043800 :=
  FiniteIntervals.of_fin 1043600 200 complete_chunk5218

lemma complete_chunk5219 : ∀ i : Fin 200, Compatible (1043800 + i.val) →
    (table.lookup (1043800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1043800 1044000 :=
  FiniteIntervals.of_fin 1043800 200 complete_chunk5219

#print axioms interval_chunk5210
end Erdos184Work.PureFiveFilter4
