import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5920 : ∀ i : Fin 200, Compatible (1184000 + i.val) →
    (table.lookup (1184000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5920 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1184000 1184200 :=
  FiniteIntervals.of_fin 1184000 200 complete_chunk5920

lemma complete_chunk5921 : ∀ i : Fin 200, Compatible (1184200 + i.val) →
    (table.lookup (1184200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5921 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1184200 1184400 :=
  FiniteIntervals.of_fin 1184200 200 complete_chunk5921

lemma complete_chunk5922 : ∀ i : Fin 200, Compatible (1184400 + i.val) →
    (table.lookup (1184400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5922 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1184400 1184600 :=
  FiniteIntervals.of_fin 1184400 200 complete_chunk5922

lemma complete_chunk5923 : ∀ i : Fin 200, Compatible (1184600 + i.val) →
    (table.lookup (1184600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5923 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1184600 1184800 :=
  FiniteIntervals.of_fin 1184600 200 complete_chunk5923

lemma complete_chunk5924 : ∀ i : Fin 200, Compatible (1184800 + i.val) →
    (table.lookup (1184800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5924 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1184800 1185000 :=
  FiniteIntervals.of_fin 1184800 200 complete_chunk5924

lemma complete_chunk5925 : ∀ i : Fin 200, Compatible (1185000 + i.val) →
    (table.lookup (1185000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5925 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1185000 1185200 :=
  FiniteIntervals.of_fin 1185000 200 complete_chunk5925

lemma complete_chunk5926 : ∀ i : Fin 200, Compatible (1185200 + i.val) →
    (table.lookup (1185200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5926 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1185200 1185400 :=
  FiniteIntervals.of_fin 1185200 200 complete_chunk5926

lemma complete_chunk5927 : ∀ i : Fin 200, Compatible (1185400 + i.val) →
    (table.lookup (1185400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5927 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1185400 1185600 :=
  FiniteIntervals.of_fin 1185400 200 complete_chunk5927

lemma complete_chunk5928 : ∀ i : Fin 200, Compatible (1185600 + i.val) →
    (table.lookup (1185600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5928 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1185600 1185800 :=
  FiniteIntervals.of_fin 1185600 200 complete_chunk5928

lemma complete_chunk5929 : ∀ i : Fin 200, Compatible (1185800 + i.val) →
    (table.lookup (1185800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5929 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1185800 1186000 :=
  FiniteIntervals.of_fin 1185800 200 complete_chunk5929

#print axioms interval_chunk5920
end Erdos184Work.PureFiveFilter4
