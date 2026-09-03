import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk620 : ∀ i : Fin 200, Compatible (124000 + i.val) →
    (table.lookup (124000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk620 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 124000 124200 :=
  FiniteIntervals.of_fin 124000 200 complete_chunk620

lemma complete_chunk621 : ∀ i : Fin 200, Compatible (124200 + i.val) →
    (table.lookup (124200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk621 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 124200 124400 :=
  FiniteIntervals.of_fin 124200 200 complete_chunk621

lemma complete_chunk622 : ∀ i : Fin 200, Compatible (124400 + i.val) →
    (table.lookup (124400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk622 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 124400 124600 :=
  FiniteIntervals.of_fin 124400 200 complete_chunk622

lemma complete_chunk623 : ∀ i : Fin 200, Compatible (124600 + i.val) →
    (table.lookup (124600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk623 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 124600 124800 :=
  FiniteIntervals.of_fin 124600 200 complete_chunk623

lemma complete_chunk624 : ∀ i : Fin 200, Compatible (124800 + i.val) →
    (table.lookup (124800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk624 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 124800 125000 :=
  FiniteIntervals.of_fin 124800 200 complete_chunk624

lemma complete_chunk625 : ∀ i : Fin 200, Compatible (125000 + i.val) →
    (table.lookup (125000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk625 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 125000 125200 :=
  FiniteIntervals.of_fin 125000 200 complete_chunk625

lemma complete_chunk626 : ∀ i : Fin 200, Compatible (125200 + i.val) →
    (table.lookup (125200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk626 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 125200 125400 :=
  FiniteIntervals.of_fin 125200 200 complete_chunk626

lemma complete_chunk627 : ∀ i : Fin 200, Compatible (125400 + i.val) →
    (table.lookup (125400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk627 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 125400 125600 :=
  FiniteIntervals.of_fin 125400 200 complete_chunk627

lemma complete_chunk628 : ∀ i : Fin 200, Compatible (125600 + i.val) →
    (table.lookup (125600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk628 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 125600 125800 :=
  FiniteIntervals.of_fin 125600 200 complete_chunk628

lemma complete_chunk629 : ∀ i : Fin 200, Compatible (125800 + i.val) →
    (table.lookup (125800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk629 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 125800 126000 :=
  FiniteIntervals.of_fin 125800 200 complete_chunk629

#print axioms interval_chunk620
end Erdos184Work.PureFiveFilter4
