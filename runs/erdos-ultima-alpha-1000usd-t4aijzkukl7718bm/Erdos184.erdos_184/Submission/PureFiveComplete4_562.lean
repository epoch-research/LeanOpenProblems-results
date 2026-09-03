import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5620 : ∀ i : Fin 200, Compatible (1124000 + i.val) →
    (table.lookup (1124000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5620 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1124000 1124200 :=
  FiniteIntervals.of_fin 1124000 200 complete_chunk5620

lemma complete_chunk5621 : ∀ i : Fin 200, Compatible (1124200 + i.val) →
    (table.lookup (1124200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5621 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1124200 1124400 :=
  FiniteIntervals.of_fin 1124200 200 complete_chunk5621

lemma complete_chunk5622 : ∀ i : Fin 200, Compatible (1124400 + i.val) →
    (table.lookup (1124400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5622 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1124400 1124600 :=
  FiniteIntervals.of_fin 1124400 200 complete_chunk5622

lemma complete_chunk5623 : ∀ i : Fin 200, Compatible (1124600 + i.val) →
    (table.lookup (1124600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5623 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1124600 1124800 :=
  FiniteIntervals.of_fin 1124600 200 complete_chunk5623

lemma complete_chunk5624 : ∀ i : Fin 200, Compatible (1124800 + i.val) →
    (table.lookup (1124800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5624 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1124800 1125000 :=
  FiniteIntervals.of_fin 1124800 200 complete_chunk5624

lemma complete_chunk5625 : ∀ i : Fin 200, Compatible (1125000 + i.val) →
    (table.lookup (1125000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5625 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1125000 1125200 :=
  FiniteIntervals.of_fin 1125000 200 complete_chunk5625

lemma complete_chunk5626 : ∀ i : Fin 200, Compatible (1125200 + i.val) →
    (table.lookup (1125200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5626 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1125200 1125400 :=
  FiniteIntervals.of_fin 1125200 200 complete_chunk5626

lemma complete_chunk5627 : ∀ i : Fin 200, Compatible (1125400 + i.val) →
    (table.lookup (1125400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5627 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1125400 1125600 :=
  FiniteIntervals.of_fin 1125400 200 complete_chunk5627

lemma complete_chunk5628 : ∀ i : Fin 200, Compatible (1125600 + i.val) →
    (table.lookup (1125600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5628 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1125600 1125800 :=
  FiniteIntervals.of_fin 1125600 200 complete_chunk5628

lemma complete_chunk5629 : ∀ i : Fin 200, Compatible (1125800 + i.val) →
    (table.lookup (1125800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5629 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1125800 1126000 :=
  FiniteIntervals.of_fin 1125800 200 complete_chunk5629

#print axioms interval_chunk5620
end Erdos184Work.PureFiveFilter4
