import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4050 : ∀ i : Fin 200, Compatible (810000 + i.val) →
    (table.lookup (810000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4050 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 810000 810200 :=
  FiniteIntervals.of_fin 810000 200 complete_chunk4050

lemma complete_chunk4051 : ∀ i : Fin 200, Compatible (810200 + i.val) →
    (table.lookup (810200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4051 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 810200 810400 :=
  FiniteIntervals.of_fin 810200 200 complete_chunk4051

lemma complete_chunk4052 : ∀ i : Fin 200, Compatible (810400 + i.val) →
    (table.lookup (810400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4052 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 810400 810600 :=
  FiniteIntervals.of_fin 810400 200 complete_chunk4052

lemma complete_chunk4053 : ∀ i : Fin 200, Compatible (810600 + i.val) →
    (table.lookup (810600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4053 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 810600 810800 :=
  FiniteIntervals.of_fin 810600 200 complete_chunk4053

lemma complete_chunk4054 : ∀ i : Fin 200, Compatible (810800 + i.val) →
    (table.lookup (810800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4054 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 810800 811000 :=
  FiniteIntervals.of_fin 810800 200 complete_chunk4054

lemma complete_chunk4055 : ∀ i : Fin 200, Compatible (811000 + i.val) →
    (table.lookup (811000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4055 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 811000 811200 :=
  FiniteIntervals.of_fin 811000 200 complete_chunk4055

lemma complete_chunk4056 : ∀ i : Fin 200, Compatible (811200 + i.val) →
    (table.lookup (811200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4056 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 811200 811400 :=
  FiniteIntervals.of_fin 811200 200 complete_chunk4056

lemma complete_chunk4057 : ∀ i : Fin 200, Compatible (811400 + i.val) →
    (table.lookup (811400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4057 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 811400 811600 :=
  FiniteIntervals.of_fin 811400 200 complete_chunk4057

lemma complete_chunk4058 : ∀ i : Fin 200, Compatible (811600 + i.val) →
    (table.lookup (811600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4058 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 811600 811800 :=
  FiniteIntervals.of_fin 811600 200 complete_chunk4058

lemma complete_chunk4059 : ∀ i : Fin 200, Compatible (811800 + i.val) →
    (table.lookup (811800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4059 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 811800 812000 :=
  FiniteIntervals.of_fin 811800 200 complete_chunk4059

#print axioms interval_chunk4050
end Erdos184Work.PureFiveFilter4
