import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3050 : ∀ i : Fin 200, Compatible (610000 + i.val) →
    (table.lookup (610000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3050 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 610000 610200 :=
  FiniteIntervals.of_fin 610000 200 complete_chunk3050

lemma complete_chunk3051 : ∀ i : Fin 200, Compatible (610200 + i.val) →
    (table.lookup (610200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3051 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 610200 610400 :=
  FiniteIntervals.of_fin 610200 200 complete_chunk3051

lemma complete_chunk3052 : ∀ i : Fin 200, Compatible (610400 + i.val) →
    (table.lookup (610400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3052 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 610400 610600 :=
  FiniteIntervals.of_fin 610400 200 complete_chunk3052

lemma complete_chunk3053 : ∀ i : Fin 200, Compatible (610600 + i.val) →
    (table.lookup (610600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3053 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 610600 610800 :=
  FiniteIntervals.of_fin 610600 200 complete_chunk3053

lemma complete_chunk3054 : ∀ i : Fin 200, Compatible (610800 + i.val) →
    (table.lookup (610800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3054 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 610800 611000 :=
  FiniteIntervals.of_fin 610800 200 complete_chunk3054

lemma complete_chunk3055 : ∀ i : Fin 200, Compatible (611000 + i.val) →
    (table.lookup (611000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3055 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 611000 611200 :=
  FiniteIntervals.of_fin 611000 200 complete_chunk3055

lemma complete_chunk3056 : ∀ i : Fin 200, Compatible (611200 + i.val) →
    (table.lookup (611200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3056 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 611200 611400 :=
  FiniteIntervals.of_fin 611200 200 complete_chunk3056

lemma complete_chunk3057 : ∀ i : Fin 200, Compatible (611400 + i.val) →
    (table.lookup (611400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3057 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 611400 611600 :=
  FiniteIntervals.of_fin 611400 200 complete_chunk3057

lemma complete_chunk3058 : ∀ i : Fin 200, Compatible (611600 + i.val) →
    (table.lookup (611600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3058 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 611600 611800 :=
  FiniteIntervals.of_fin 611600 200 complete_chunk3058

lemma complete_chunk3059 : ∀ i : Fin 200, Compatible (611800 + i.val) →
    (table.lookup (611800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3059 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 611800 612000 :=
  FiniteIntervals.of_fin 611800 200 complete_chunk3059

#print axioms interval_chunk3050
end Erdos184Work.PureFiveFilter4
