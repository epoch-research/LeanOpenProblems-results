import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2390 : ∀ i : Fin 200, Compatible (478000 + i.val) →
    (table.lookup (478000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2390 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 478000 478200 :=
  FiniteIntervals.of_fin 478000 200 complete_chunk2390

lemma complete_chunk2391 : ∀ i : Fin 200, Compatible (478200 + i.val) →
    (table.lookup (478200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2391 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 478200 478400 :=
  FiniteIntervals.of_fin 478200 200 complete_chunk2391

lemma complete_chunk2392 : ∀ i : Fin 200, Compatible (478400 + i.val) →
    (table.lookup (478400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2392 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 478400 478600 :=
  FiniteIntervals.of_fin 478400 200 complete_chunk2392

lemma complete_chunk2393 : ∀ i : Fin 200, Compatible (478600 + i.val) →
    (table.lookup (478600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2393 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 478600 478800 :=
  FiniteIntervals.of_fin 478600 200 complete_chunk2393

lemma complete_chunk2394 : ∀ i : Fin 200, Compatible (478800 + i.val) →
    (table.lookup (478800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2394 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 478800 479000 :=
  FiniteIntervals.of_fin 478800 200 complete_chunk2394

lemma complete_chunk2395 : ∀ i : Fin 200, Compatible (479000 + i.val) →
    (table.lookup (479000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2395 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 479000 479200 :=
  FiniteIntervals.of_fin 479000 200 complete_chunk2395

lemma complete_chunk2396 : ∀ i : Fin 200, Compatible (479200 + i.val) →
    (table.lookup (479200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2396 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 479200 479400 :=
  FiniteIntervals.of_fin 479200 200 complete_chunk2396

lemma complete_chunk2397 : ∀ i : Fin 200, Compatible (479400 + i.val) →
    (table.lookup (479400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2397 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 479400 479600 :=
  FiniteIntervals.of_fin 479400 200 complete_chunk2397

lemma complete_chunk2398 : ∀ i : Fin 200, Compatible (479600 + i.val) →
    (table.lookup (479600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2398 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 479600 479800 :=
  FiniteIntervals.of_fin 479600 200 complete_chunk2398

lemma complete_chunk2399 : ∀ i : Fin 200, Compatible (479800 + i.val) →
    (table.lookup (479800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2399 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 479800 480000 :=
  FiniteIntervals.of_fin 479800 200 complete_chunk2399

#print axioms interval_chunk2390
end Erdos184Work.PureFiveFilter4
