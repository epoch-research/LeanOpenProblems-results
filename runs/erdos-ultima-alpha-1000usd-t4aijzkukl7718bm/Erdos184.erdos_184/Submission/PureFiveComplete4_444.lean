import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4440 : ∀ i : Fin 200, Compatible (888000 + i.val) →
    (table.lookup (888000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4440 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 888000 888200 :=
  FiniteIntervals.of_fin 888000 200 complete_chunk4440

lemma complete_chunk4441 : ∀ i : Fin 200, Compatible (888200 + i.val) →
    (table.lookup (888200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4441 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 888200 888400 :=
  FiniteIntervals.of_fin 888200 200 complete_chunk4441

lemma complete_chunk4442 : ∀ i : Fin 200, Compatible (888400 + i.val) →
    (table.lookup (888400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4442 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 888400 888600 :=
  FiniteIntervals.of_fin 888400 200 complete_chunk4442

lemma complete_chunk4443 : ∀ i : Fin 200, Compatible (888600 + i.val) →
    (table.lookup (888600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4443 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 888600 888800 :=
  FiniteIntervals.of_fin 888600 200 complete_chunk4443

lemma complete_chunk4444 : ∀ i : Fin 200, Compatible (888800 + i.val) →
    (table.lookup (888800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4444 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 888800 889000 :=
  FiniteIntervals.of_fin 888800 200 complete_chunk4444

lemma complete_chunk4445 : ∀ i : Fin 200, Compatible (889000 + i.val) →
    (table.lookup (889000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4445 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 889000 889200 :=
  FiniteIntervals.of_fin 889000 200 complete_chunk4445

lemma complete_chunk4446 : ∀ i : Fin 200, Compatible (889200 + i.val) →
    (table.lookup (889200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4446 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 889200 889400 :=
  FiniteIntervals.of_fin 889200 200 complete_chunk4446

lemma complete_chunk4447 : ∀ i : Fin 200, Compatible (889400 + i.val) →
    (table.lookup (889400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4447 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 889400 889600 :=
  FiniteIntervals.of_fin 889400 200 complete_chunk4447

lemma complete_chunk4448 : ∀ i : Fin 200, Compatible (889600 + i.val) →
    (table.lookup (889600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4448 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 889600 889800 :=
  FiniteIntervals.of_fin 889600 200 complete_chunk4448

lemma complete_chunk4449 : ∀ i : Fin 200, Compatible (889800 + i.val) →
    (table.lookup (889800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4449 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 889800 890000 :=
  FiniteIntervals.of_fin 889800 200 complete_chunk4449

#print axioms interval_chunk4440
end Erdos184Work.PureFiveFilter4
