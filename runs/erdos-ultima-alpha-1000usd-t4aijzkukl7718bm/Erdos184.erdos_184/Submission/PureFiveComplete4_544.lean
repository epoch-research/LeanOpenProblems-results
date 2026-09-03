import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5440 : ∀ i : Fin 200, Compatible (1088000 + i.val) →
    (table.lookup (1088000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5440 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1088000 1088200 :=
  FiniteIntervals.of_fin 1088000 200 complete_chunk5440

lemma complete_chunk5441 : ∀ i : Fin 200, Compatible (1088200 + i.val) →
    (table.lookup (1088200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5441 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1088200 1088400 :=
  FiniteIntervals.of_fin 1088200 200 complete_chunk5441

lemma complete_chunk5442 : ∀ i : Fin 200, Compatible (1088400 + i.val) →
    (table.lookup (1088400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5442 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1088400 1088600 :=
  FiniteIntervals.of_fin 1088400 200 complete_chunk5442

lemma complete_chunk5443 : ∀ i : Fin 200, Compatible (1088600 + i.val) →
    (table.lookup (1088600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5443 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1088600 1088800 :=
  FiniteIntervals.of_fin 1088600 200 complete_chunk5443

lemma complete_chunk5444 : ∀ i : Fin 200, Compatible (1088800 + i.val) →
    (table.lookup (1088800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5444 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1088800 1089000 :=
  FiniteIntervals.of_fin 1088800 200 complete_chunk5444

lemma complete_chunk5445 : ∀ i : Fin 200, Compatible (1089000 + i.val) →
    (table.lookup (1089000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5445 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1089000 1089200 :=
  FiniteIntervals.of_fin 1089000 200 complete_chunk5445

lemma complete_chunk5446 : ∀ i : Fin 200, Compatible (1089200 + i.val) →
    (table.lookup (1089200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5446 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1089200 1089400 :=
  FiniteIntervals.of_fin 1089200 200 complete_chunk5446

lemma complete_chunk5447 : ∀ i : Fin 200, Compatible (1089400 + i.val) →
    (table.lookup (1089400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5447 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1089400 1089600 :=
  FiniteIntervals.of_fin 1089400 200 complete_chunk5447

lemma complete_chunk5448 : ∀ i : Fin 200, Compatible (1089600 + i.val) →
    (table.lookup (1089600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5448 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1089600 1089800 :=
  FiniteIntervals.of_fin 1089600 200 complete_chunk5448

lemma complete_chunk5449 : ∀ i : Fin 200, Compatible (1089800 + i.val) →
    (table.lookup (1089800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5449 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1089800 1090000 :=
  FiniteIntervals.of_fin 1089800 200 complete_chunk5449

#print axioms interval_chunk5440
end Erdos184Work.PureFiveFilter4
