import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3380 : ∀ i : Fin 200, Compatible (676000 + i.val) →
    (table.lookup (676000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3380 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 676000 676200 :=
  FiniteIntervals.of_fin 676000 200 complete_chunk3380

lemma complete_chunk3381 : ∀ i : Fin 200, Compatible (676200 + i.val) →
    (table.lookup (676200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3381 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 676200 676400 :=
  FiniteIntervals.of_fin 676200 200 complete_chunk3381

lemma complete_chunk3382 : ∀ i : Fin 200, Compatible (676400 + i.val) →
    (table.lookup (676400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3382 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 676400 676600 :=
  FiniteIntervals.of_fin 676400 200 complete_chunk3382

lemma complete_chunk3383 : ∀ i : Fin 200, Compatible (676600 + i.val) →
    (table.lookup (676600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3383 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 676600 676800 :=
  FiniteIntervals.of_fin 676600 200 complete_chunk3383

lemma complete_chunk3384 : ∀ i : Fin 200, Compatible (676800 + i.val) →
    (table.lookup (676800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3384 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 676800 677000 :=
  FiniteIntervals.of_fin 676800 200 complete_chunk3384

lemma complete_chunk3385 : ∀ i : Fin 200, Compatible (677000 + i.val) →
    (table.lookup (677000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3385 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 677000 677200 :=
  FiniteIntervals.of_fin 677000 200 complete_chunk3385

lemma complete_chunk3386 : ∀ i : Fin 200, Compatible (677200 + i.val) →
    (table.lookup (677200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3386 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 677200 677400 :=
  FiniteIntervals.of_fin 677200 200 complete_chunk3386

lemma complete_chunk3387 : ∀ i : Fin 200, Compatible (677400 + i.val) →
    (table.lookup (677400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3387 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 677400 677600 :=
  FiniteIntervals.of_fin 677400 200 complete_chunk3387

lemma complete_chunk3388 : ∀ i : Fin 200, Compatible (677600 + i.val) →
    (table.lookup (677600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3388 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 677600 677800 :=
  FiniteIntervals.of_fin 677600 200 complete_chunk3388

lemma complete_chunk3389 : ∀ i : Fin 200, Compatible (677800 + i.val) →
    (table.lookup (677800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3389 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 677800 678000 :=
  FiniteIntervals.of_fin 677800 200 complete_chunk3389

#print axioms interval_chunk3380
end Erdos184Work.PureFiveFilter4
