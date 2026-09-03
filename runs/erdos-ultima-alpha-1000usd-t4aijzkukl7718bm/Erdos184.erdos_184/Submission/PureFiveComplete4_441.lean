import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4410 : ∀ i : Fin 200, Compatible (882000 + i.val) →
    (table.lookup (882000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4410 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 882000 882200 :=
  FiniteIntervals.of_fin 882000 200 complete_chunk4410

lemma complete_chunk4411 : ∀ i : Fin 200, Compatible (882200 + i.val) →
    (table.lookup (882200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4411 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 882200 882400 :=
  FiniteIntervals.of_fin 882200 200 complete_chunk4411

lemma complete_chunk4412 : ∀ i : Fin 200, Compatible (882400 + i.val) →
    (table.lookup (882400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4412 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 882400 882600 :=
  FiniteIntervals.of_fin 882400 200 complete_chunk4412

lemma complete_chunk4413 : ∀ i : Fin 200, Compatible (882600 + i.val) →
    (table.lookup (882600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4413 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 882600 882800 :=
  FiniteIntervals.of_fin 882600 200 complete_chunk4413

lemma complete_chunk4414 : ∀ i : Fin 200, Compatible (882800 + i.val) →
    (table.lookup (882800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4414 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 882800 883000 :=
  FiniteIntervals.of_fin 882800 200 complete_chunk4414

lemma complete_chunk4415 : ∀ i : Fin 200, Compatible (883000 + i.val) →
    (table.lookup (883000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4415 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 883000 883200 :=
  FiniteIntervals.of_fin 883000 200 complete_chunk4415

lemma complete_chunk4416 : ∀ i : Fin 200, Compatible (883200 + i.val) →
    (table.lookup (883200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4416 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 883200 883400 :=
  FiniteIntervals.of_fin 883200 200 complete_chunk4416

lemma complete_chunk4417 : ∀ i : Fin 200, Compatible (883400 + i.val) →
    (table.lookup (883400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4417 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 883400 883600 :=
  FiniteIntervals.of_fin 883400 200 complete_chunk4417

lemma complete_chunk4418 : ∀ i : Fin 200, Compatible (883600 + i.val) →
    (table.lookup (883600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4418 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 883600 883800 :=
  FiniteIntervals.of_fin 883600 200 complete_chunk4418

lemma complete_chunk4419 : ∀ i : Fin 200, Compatible (883800 + i.val) →
    (table.lookup (883800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4419 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 883800 884000 :=
  FiniteIntervals.of_fin 883800 200 complete_chunk4419

#print axioms interval_chunk4410
end Erdos184Work.PureFiveFilter4
