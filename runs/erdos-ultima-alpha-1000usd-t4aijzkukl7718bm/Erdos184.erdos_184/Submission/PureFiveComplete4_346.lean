import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3460 : ∀ i : Fin 200, Compatible (692000 + i.val) →
    (table.lookup (692000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3460 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 692000 692200 :=
  FiniteIntervals.of_fin 692000 200 complete_chunk3460

lemma complete_chunk3461 : ∀ i : Fin 200, Compatible (692200 + i.val) →
    (table.lookup (692200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3461 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 692200 692400 :=
  FiniteIntervals.of_fin 692200 200 complete_chunk3461

lemma complete_chunk3462 : ∀ i : Fin 200, Compatible (692400 + i.val) →
    (table.lookup (692400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3462 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 692400 692600 :=
  FiniteIntervals.of_fin 692400 200 complete_chunk3462

lemma complete_chunk3463 : ∀ i : Fin 200, Compatible (692600 + i.val) →
    (table.lookup (692600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3463 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 692600 692800 :=
  FiniteIntervals.of_fin 692600 200 complete_chunk3463

lemma complete_chunk3464 : ∀ i : Fin 200, Compatible (692800 + i.val) →
    (table.lookup (692800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3464 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 692800 693000 :=
  FiniteIntervals.of_fin 692800 200 complete_chunk3464

lemma complete_chunk3465 : ∀ i : Fin 200, Compatible (693000 + i.val) →
    (table.lookup (693000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3465 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 693000 693200 :=
  FiniteIntervals.of_fin 693000 200 complete_chunk3465

lemma complete_chunk3466 : ∀ i : Fin 200, Compatible (693200 + i.val) →
    (table.lookup (693200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3466 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 693200 693400 :=
  FiniteIntervals.of_fin 693200 200 complete_chunk3466

lemma complete_chunk3467 : ∀ i : Fin 200, Compatible (693400 + i.val) →
    (table.lookup (693400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3467 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 693400 693600 :=
  FiniteIntervals.of_fin 693400 200 complete_chunk3467

lemma complete_chunk3468 : ∀ i : Fin 200, Compatible (693600 + i.val) →
    (table.lookup (693600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3468 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 693600 693800 :=
  FiniteIntervals.of_fin 693600 200 complete_chunk3468

lemma complete_chunk3469 : ∀ i : Fin 200, Compatible (693800 + i.val) →
    (table.lookup (693800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3469 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 693800 694000 :=
  FiniteIntervals.of_fin 693800 200 complete_chunk3469

#print axioms interval_chunk3460
end Erdos184Work.PureFiveFilter4
