import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3270 : ∀ i : Fin 200, Compatible (654000 + i.val) →
    (table.lookup (654000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3270 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 654000 654200 :=
  FiniteIntervals.of_fin 654000 200 complete_chunk3270

lemma complete_chunk3271 : ∀ i : Fin 200, Compatible (654200 + i.val) →
    (table.lookup (654200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3271 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 654200 654400 :=
  FiniteIntervals.of_fin 654200 200 complete_chunk3271

lemma complete_chunk3272 : ∀ i : Fin 200, Compatible (654400 + i.val) →
    (table.lookup (654400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3272 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 654400 654600 :=
  FiniteIntervals.of_fin 654400 200 complete_chunk3272

lemma complete_chunk3273 : ∀ i : Fin 200, Compatible (654600 + i.val) →
    (table.lookup (654600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3273 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 654600 654800 :=
  FiniteIntervals.of_fin 654600 200 complete_chunk3273

lemma complete_chunk3274 : ∀ i : Fin 200, Compatible (654800 + i.val) →
    (table.lookup (654800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3274 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 654800 655000 :=
  FiniteIntervals.of_fin 654800 200 complete_chunk3274

lemma complete_chunk3275 : ∀ i : Fin 200, Compatible (655000 + i.val) →
    (table.lookup (655000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3275 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 655000 655200 :=
  FiniteIntervals.of_fin 655000 200 complete_chunk3275

lemma complete_chunk3276 : ∀ i : Fin 200, Compatible (655200 + i.val) →
    (table.lookup (655200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3276 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 655200 655400 :=
  FiniteIntervals.of_fin 655200 200 complete_chunk3276

lemma complete_chunk3277 : ∀ i : Fin 200, Compatible (655400 + i.val) →
    (table.lookup (655400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3277 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 655400 655600 :=
  FiniteIntervals.of_fin 655400 200 complete_chunk3277

lemma complete_chunk3278 : ∀ i : Fin 200, Compatible (655600 + i.val) →
    (table.lookup (655600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3278 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 655600 655800 :=
  FiniteIntervals.of_fin 655600 200 complete_chunk3278

lemma complete_chunk3279 : ∀ i : Fin 200, Compatible (655800 + i.val) →
    (table.lookup (655800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3279 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 655800 656000 :=
  FiniteIntervals.of_fin 655800 200 complete_chunk3279

#print axioms interval_chunk3270
end Erdos184Work.PureFiveFilter4
