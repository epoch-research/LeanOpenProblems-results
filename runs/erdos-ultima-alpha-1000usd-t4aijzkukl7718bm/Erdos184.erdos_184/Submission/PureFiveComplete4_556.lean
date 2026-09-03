import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5560 : ∀ i : Fin 200, Compatible (1112000 + i.val) →
    (table.lookup (1112000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5560 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1112000 1112200 :=
  FiniteIntervals.of_fin 1112000 200 complete_chunk5560

lemma complete_chunk5561 : ∀ i : Fin 200, Compatible (1112200 + i.val) →
    (table.lookup (1112200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5561 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1112200 1112400 :=
  FiniteIntervals.of_fin 1112200 200 complete_chunk5561

lemma complete_chunk5562 : ∀ i : Fin 200, Compatible (1112400 + i.val) →
    (table.lookup (1112400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5562 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1112400 1112600 :=
  FiniteIntervals.of_fin 1112400 200 complete_chunk5562

lemma complete_chunk5563 : ∀ i : Fin 200, Compatible (1112600 + i.val) →
    (table.lookup (1112600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5563 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1112600 1112800 :=
  FiniteIntervals.of_fin 1112600 200 complete_chunk5563

lemma complete_chunk5564 : ∀ i : Fin 200, Compatible (1112800 + i.val) →
    (table.lookup (1112800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5564 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1112800 1113000 :=
  FiniteIntervals.of_fin 1112800 200 complete_chunk5564

lemma complete_chunk5565 : ∀ i : Fin 200, Compatible (1113000 + i.val) →
    (table.lookup (1113000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5565 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1113000 1113200 :=
  FiniteIntervals.of_fin 1113000 200 complete_chunk5565

lemma complete_chunk5566 : ∀ i : Fin 200, Compatible (1113200 + i.val) →
    (table.lookup (1113200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5566 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1113200 1113400 :=
  FiniteIntervals.of_fin 1113200 200 complete_chunk5566

lemma complete_chunk5567 : ∀ i : Fin 200, Compatible (1113400 + i.val) →
    (table.lookup (1113400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5567 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1113400 1113600 :=
  FiniteIntervals.of_fin 1113400 200 complete_chunk5567

lemma complete_chunk5568 : ∀ i : Fin 200, Compatible (1113600 + i.val) →
    (table.lookup (1113600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5568 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1113600 1113800 :=
  FiniteIntervals.of_fin 1113600 200 complete_chunk5568

lemma complete_chunk5569 : ∀ i : Fin 200, Compatible (1113800 + i.val) →
    (table.lookup (1113800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5569 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1113800 1114000 :=
  FiniteIntervals.of_fin 1113800 200 complete_chunk5569

#print axioms interval_chunk5560
end Erdos184Work.PureFiveFilter4
