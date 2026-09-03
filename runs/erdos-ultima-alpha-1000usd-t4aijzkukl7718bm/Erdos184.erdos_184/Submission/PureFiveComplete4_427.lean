import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4270 : ∀ i : Fin 200, Compatible (854000 + i.val) →
    (table.lookup (854000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4270 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 854000 854200 :=
  FiniteIntervals.of_fin 854000 200 complete_chunk4270

lemma complete_chunk4271 : ∀ i : Fin 200, Compatible (854200 + i.val) →
    (table.lookup (854200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4271 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 854200 854400 :=
  FiniteIntervals.of_fin 854200 200 complete_chunk4271

lemma complete_chunk4272 : ∀ i : Fin 200, Compatible (854400 + i.val) →
    (table.lookup (854400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4272 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 854400 854600 :=
  FiniteIntervals.of_fin 854400 200 complete_chunk4272

lemma complete_chunk4273 : ∀ i : Fin 200, Compatible (854600 + i.val) →
    (table.lookup (854600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4273 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 854600 854800 :=
  FiniteIntervals.of_fin 854600 200 complete_chunk4273

lemma complete_chunk4274 : ∀ i : Fin 200, Compatible (854800 + i.val) →
    (table.lookup (854800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4274 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 854800 855000 :=
  FiniteIntervals.of_fin 854800 200 complete_chunk4274

lemma complete_chunk4275 : ∀ i : Fin 200, Compatible (855000 + i.val) →
    (table.lookup (855000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4275 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 855000 855200 :=
  FiniteIntervals.of_fin 855000 200 complete_chunk4275

lemma complete_chunk4276 : ∀ i : Fin 200, Compatible (855200 + i.val) →
    (table.lookup (855200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4276 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 855200 855400 :=
  FiniteIntervals.of_fin 855200 200 complete_chunk4276

lemma complete_chunk4277 : ∀ i : Fin 200, Compatible (855400 + i.val) →
    (table.lookup (855400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4277 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 855400 855600 :=
  FiniteIntervals.of_fin 855400 200 complete_chunk4277

lemma complete_chunk4278 : ∀ i : Fin 200, Compatible (855600 + i.val) →
    (table.lookup (855600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4278 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 855600 855800 :=
  FiniteIntervals.of_fin 855600 200 complete_chunk4278

lemma complete_chunk4279 : ∀ i : Fin 200, Compatible (855800 + i.val) →
    (table.lookup (855800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4279 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 855800 856000 :=
  FiniteIntervals.of_fin 855800 200 complete_chunk4279

#print axioms interval_chunk4270
end Erdos184Work.PureFiveFilter4
