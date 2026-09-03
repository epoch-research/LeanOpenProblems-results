import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4360 : ∀ i : Fin 200, Compatible (872000 + i.val) →
    (table.lookup (872000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4360 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 872000 872200 :=
  FiniteIntervals.of_fin 872000 200 complete_chunk4360

lemma complete_chunk4361 : ∀ i : Fin 200, Compatible (872200 + i.val) →
    (table.lookup (872200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4361 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 872200 872400 :=
  FiniteIntervals.of_fin 872200 200 complete_chunk4361

lemma complete_chunk4362 : ∀ i : Fin 200, Compatible (872400 + i.val) →
    (table.lookup (872400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4362 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 872400 872600 :=
  FiniteIntervals.of_fin 872400 200 complete_chunk4362

lemma complete_chunk4363 : ∀ i : Fin 200, Compatible (872600 + i.val) →
    (table.lookup (872600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4363 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 872600 872800 :=
  FiniteIntervals.of_fin 872600 200 complete_chunk4363

lemma complete_chunk4364 : ∀ i : Fin 200, Compatible (872800 + i.val) →
    (table.lookup (872800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4364 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 872800 873000 :=
  FiniteIntervals.of_fin 872800 200 complete_chunk4364

lemma complete_chunk4365 : ∀ i : Fin 200, Compatible (873000 + i.val) →
    (table.lookup (873000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4365 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 873000 873200 :=
  FiniteIntervals.of_fin 873000 200 complete_chunk4365

lemma complete_chunk4366 : ∀ i : Fin 200, Compatible (873200 + i.val) →
    (table.lookup (873200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4366 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 873200 873400 :=
  FiniteIntervals.of_fin 873200 200 complete_chunk4366

lemma complete_chunk4367 : ∀ i : Fin 200, Compatible (873400 + i.val) →
    (table.lookup (873400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4367 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 873400 873600 :=
  FiniteIntervals.of_fin 873400 200 complete_chunk4367

lemma complete_chunk4368 : ∀ i : Fin 200, Compatible (873600 + i.val) →
    (table.lookup (873600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4368 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 873600 873800 :=
  FiniteIntervals.of_fin 873600 200 complete_chunk4368

lemma complete_chunk4369 : ∀ i : Fin 200, Compatible (873800 + i.val) →
    (table.lookup (873800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4369 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 873800 874000 :=
  FiniteIntervals.of_fin 873800 200 complete_chunk4369

#print axioms interval_chunk4360
end Erdos184Work.PureFiveFilter4
