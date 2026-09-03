import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk70 : ∀ i : Fin 200, Compatible (14000 + i.val) →
    (table.lookup (14000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk70 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 14000 14200 :=
  FiniteIntervals.of_fin 14000 200 complete_chunk70

lemma complete_chunk71 : ∀ i : Fin 200, Compatible (14200 + i.val) →
    (table.lookup (14200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk71 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 14200 14400 :=
  FiniteIntervals.of_fin 14200 200 complete_chunk71

lemma complete_chunk72 : ∀ i : Fin 200, Compatible (14400 + i.val) →
    (table.lookup (14400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk72 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 14400 14600 :=
  FiniteIntervals.of_fin 14400 200 complete_chunk72

lemma complete_chunk73 : ∀ i : Fin 200, Compatible (14600 + i.val) →
    (table.lookup (14600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk73 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 14600 14800 :=
  FiniteIntervals.of_fin 14600 200 complete_chunk73

lemma complete_chunk74 : ∀ i : Fin 200, Compatible (14800 + i.val) →
    (table.lookup (14800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk74 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 14800 15000 :=
  FiniteIntervals.of_fin 14800 200 complete_chunk74

lemma complete_chunk75 : ∀ i : Fin 200, Compatible (15000 + i.val) →
    (table.lookup (15000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk75 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 15000 15200 :=
  FiniteIntervals.of_fin 15000 200 complete_chunk75

lemma complete_chunk76 : ∀ i : Fin 200, Compatible (15200 + i.val) →
    (table.lookup (15200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk76 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 15200 15400 :=
  FiniteIntervals.of_fin 15200 200 complete_chunk76

lemma complete_chunk77 : ∀ i : Fin 200, Compatible (15400 + i.val) →
    (table.lookup (15400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk77 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 15400 15600 :=
  FiniteIntervals.of_fin 15400 200 complete_chunk77

lemma complete_chunk78 : ∀ i : Fin 200, Compatible (15600 + i.val) →
    (table.lookup (15600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk78 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 15600 15800 :=
  FiniteIntervals.of_fin 15600 200 complete_chunk78

lemma complete_chunk79 : ∀ i : Fin 200, Compatible (15800 + i.val) →
    (table.lookup (15800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk79 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 15800 16000 :=
  FiniteIntervals.of_fin 15800 200 complete_chunk79

#print axioms interval_chunk70
end Erdos184Work.PureFiveFilter3
