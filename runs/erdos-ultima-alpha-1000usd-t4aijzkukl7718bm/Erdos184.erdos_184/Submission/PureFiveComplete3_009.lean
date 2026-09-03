import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk90 : ∀ i : Fin 200, Compatible (18000 + i.val) →
    (table.lookup (18000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk90 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 18000 18200 :=
  FiniteIntervals.of_fin 18000 200 complete_chunk90

lemma complete_chunk91 : ∀ i : Fin 200, Compatible (18200 + i.val) →
    (table.lookup (18200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk91 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 18200 18400 :=
  FiniteIntervals.of_fin 18200 200 complete_chunk91

lemma complete_chunk92 : ∀ i : Fin 200, Compatible (18400 + i.val) →
    (table.lookup (18400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk92 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 18400 18600 :=
  FiniteIntervals.of_fin 18400 200 complete_chunk92

lemma complete_chunk93 : ∀ i : Fin 200, Compatible (18600 + i.val) →
    (table.lookup (18600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk93 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 18600 18800 :=
  FiniteIntervals.of_fin 18600 200 complete_chunk93

lemma complete_chunk94 : ∀ i : Fin 200, Compatible (18800 + i.val) →
    (table.lookup (18800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk94 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 18800 19000 :=
  FiniteIntervals.of_fin 18800 200 complete_chunk94

lemma complete_chunk95 : ∀ i : Fin 200, Compatible (19000 + i.val) →
    (table.lookup (19000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk95 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 19000 19200 :=
  FiniteIntervals.of_fin 19000 200 complete_chunk95

lemma complete_chunk96 : ∀ i : Fin 200, Compatible (19200 + i.val) →
    (table.lookup (19200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk96 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 19200 19400 :=
  FiniteIntervals.of_fin 19200 200 complete_chunk96

lemma complete_chunk97 : ∀ i : Fin 200, Compatible (19400 + i.val) →
    (table.lookup (19400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk97 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 19400 19600 :=
  FiniteIntervals.of_fin 19400 200 complete_chunk97

lemma complete_chunk98 : ∀ i : Fin 200, Compatible (19600 + i.val) →
    (table.lookup (19600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk98 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 19600 19800 :=
  FiniteIntervals.of_fin 19600 200 complete_chunk98

lemma complete_chunk99 : ∀ i : Fin 200, Compatible (19800 + i.val) →
    (table.lookup (19800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk99 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 19800 20000 :=
  FiniteIntervals.of_fin 19800 200 complete_chunk99

#print axioms interval_chunk90
end Erdos184Work.PureFiveFilter3
