import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3500 : ∀ i : Fin 200, Compatible (700000 + i.val) →
    (table.lookup (700000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3500 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 700000 700200 :=
  FiniteIntervals.of_fin 700000 200 complete_chunk3500

lemma complete_chunk3501 : ∀ i : Fin 200, Compatible (700200 + i.val) →
    (table.lookup (700200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3501 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 700200 700400 :=
  FiniteIntervals.of_fin 700200 200 complete_chunk3501

lemma complete_chunk3502 : ∀ i : Fin 200, Compatible (700400 + i.val) →
    (table.lookup (700400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3502 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 700400 700600 :=
  FiniteIntervals.of_fin 700400 200 complete_chunk3502

lemma complete_chunk3503 : ∀ i : Fin 200, Compatible (700600 + i.val) →
    (table.lookup (700600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3503 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 700600 700800 :=
  FiniteIntervals.of_fin 700600 200 complete_chunk3503

lemma complete_chunk3504 : ∀ i : Fin 200, Compatible (700800 + i.val) →
    (table.lookup (700800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3504 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 700800 701000 :=
  FiniteIntervals.of_fin 700800 200 complete_chunk3504

lemma complete_chunk3505 : ∀ i : Fin 200, Compatible (701000 + i.val) →
    (table.lookup (701000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3505 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 701000 701200 :=
  FiniteIntervals.of_fin 701000 200 complete_chunk3505

lemma complete_chunk3506 : ∀ i : Fin 200, Compatible (701200 + i.val) →
    (table.lookup (701200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3506 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 701200 701400 :=
  FiniteIntervals.of_fin 701200 200 complete_chunk3506

lemma complete_chunk3507 : ∀ i : Fin 200, Compatible (701400 + i.val) →
    (table.lookup (701400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3507 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 701400 701600 :=
  FiniteIntervals.of_fin 701400 200 complete_chunk3507

lemma complete_chunk3508 : ∀ i : Fin 200, Compatible (701600 + i.val) →
    (table.lookup (701600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3508 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 701600 701800 :=
  FiniteIntervals.of_fin 701600 200 complete_chunk3508

lemma complete_chunk3509 : ∀ i : Fin 200, Compatible (701800 + i.val) →
    (table.lookup (701800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3509 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 701800 702000 :=
  FiniteIntervals.of_fin 701800 200 complete_chunk3509

#print axioms interval_chunk3500
end Erdos184Work.PureFiveFilter4
