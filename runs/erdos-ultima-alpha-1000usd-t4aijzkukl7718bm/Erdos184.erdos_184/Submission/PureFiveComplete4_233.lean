import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2330 : ∀ i : Fin 200, Compatible (466000 + i.val) →
    (table.lookup (466000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2330 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 466000 466200 :=
  FiniteIntervals.of_fin 466000 200 complete_chunk2330

lemma complete_chunk2331 : ∀ i : Fin 200, Compatible (466200 + i.val) →
    (table.lookup (466200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2331 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 466200 466400 :=
  FiniteIntervals.of_fin 466200 200 complete_chunk2331

lemma complete_chunk2332 : ∀ i : Fin 200, Compatible (466400 + i.val) →
    (table.lookup (466400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2332 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 466400 466600 :=
  FiniteIntervals.of_fin 466400 200 complete_chunk2332

lemma complete_chunk2333 : ∀ i : Fin 200, Compatible (466600 + i.val) →
    (table.lookup (466600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2333 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 466600 466800 :=
  FiniteIntervals.of_fin 466600 200 complete_chunk2333

lemma complete_chunk2334 : ∀ i : Fin 200, Compatible (466800 + i.val) →
    (table.lookup (466800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2334 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 466800 467000 :=
  FiniteIntervals.of_fin 466800 200 complete_chunk2334

lemma complete_chunk2335 : ∀ i : Fin 200, Compatible (467000 + i.val) →
    (table.lookup (467000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2335 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 467000 467200 :=
  FiniteIntervals.of_fin 467000 200 complete_chunk2335

lemma complete_chunk2336 : ∀ i : Fin 200, Compatible (467200 + i.val) →
    (table.lookup (467200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2336 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 467200 467400 :=
  FiniteIntervals.of_fin 467200 200 complete_chunk2336

lemma complete_chunk2337 : ∀ i : Fin 200, Compatible (467400 + i.val) →
    (table.lookup (467400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2337 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 467400 467600 :=
  FiniteIntervals.of_fin 467400 200 complete_chunk2337

lemma complete_chunk2338 : ∀ i : Fin 200, Compatible (467600 + i.val) →
    (table.lookup (467600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2338 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 467600 467800 :=
  FiniteIntervals.of_fin 467600 200 complete_chunk2338

lemma complete_chunk2339 : ∀ i : Fin 200, Compatible (467800 + i.val) →
    (table.lookup (467800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2339 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 467800 468000 :=
  FiniteIntervals.of_fin 467800 200 complete_chunk2339

#print axioms interval_chunk2330
end Erdos184Work.PureFiveFilter4
