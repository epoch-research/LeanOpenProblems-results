import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk920 : ∀ i : Fin 200, Compatible (184000 + i.val) →
    (table.lookup (184000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk920 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 184000 184200 :=
  FiniteIntervals.of_fin 184000 200 complete_chunk920

lemma complete_chunk921 : ∀ i : Fin 200, Compatible (184200 + i.val) →
    (table.lookup (184200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk921 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 184200 184400 :=
  FiniteIntervals.of_fin 184200 200 complete_chunk921

lemma complete_chunk922 : ∀ i : Fin 200, Compatible (184400 + i.val) →
    (table.lookup (184400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk922 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 184400 184600 :=
  FiniteIntervals.of_fin 184400 200 complete_chunk922

lemma complete_chunk923 : ∀ i : Fin 200, Compatible (184600 + i.val) →
    (table.lookup (184600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk923 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 184600 184800 :=
  FiniteIntervals.of_fin 184600 200 complete_chunk923

lemma complete_chunk924 : ∀ i : Fin 200, Compatible (184800 + i.val) →
    (table.lookup (184800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk924 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 184800 185000 :=
  FiniteIntervals.of_fin 184800 200 complete_chunk924

lemma complete_chunk925 : ∀ i : Fin 200, Compatible (185000 + i.val) →
    (table.lookup (185000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk925 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 185000 185200 :=
  FiniteIntervals.of_fin 185000 200 complete_chunk925

lemma complete_chunk926 : ∀ i : Fin 200, Compatible (185200 + i.val) →
    (table.lookup (185200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk926 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 185200 185400 :=
  FiniteIntervals.of_fin 185200 200 complete_chunk926

lemma complete_chunk927 : ∀ i : Fin 200, Compatible (185400 + i.val) →
    (table.lookup (185400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk927 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 185400 185600 :=
  FiniteIntervals.of_fin 185400 200 complete_chunk927

lemma complete_chunk928 : ∀ i : Fin 200, Compatible (185600 + i.val) →
    (table.lookup (185600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk928 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 185600 185800 :=
  FiniteIntervals.of_fin 185600 200 complete_chunk928

lemma complete_chunk929 : ∀ i : Fin 200, Compatible (185800 + i.val) →
    (table.lookup (185800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk929 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 185800 186000 :=
  FiniteIntervals.of_fin 185800 200 complete_chunk929

#print axioms interval_chunk920
end Erdos184Work.PureFiveFilter4
