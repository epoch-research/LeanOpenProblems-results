import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk40 : ∀ i : Fin 200, Compatible (8000 + i.val) →
    (table.lookup (8000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk40 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 8000 8200 :=
  FiniteIntervals.of_fin 8000 200 complete_chunk40

lemma complete_chunk41 : ∀ i : Fin 200, Compatible (8200 + i.val) →
    (table.lookup (8200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk41 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 8200 8400 :=
  FiniteIntervals.of_fin 8200 200 complete_chunk41

lemma complete_chunk42 : ∀ i : Fin 200, Compatible (8400 + i.val) →
    (table.lookup (8400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk42 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 8400 8600 :=
  FiniteIntervals.of_fin 8400 200 complete_chunk42

lemma complete_chunk43 : ∀ i : Fin 200, Compatible (8600 + i.val) →
    (table.lookup (8600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk43 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 8600 8800 :=
  FiniteIntervals.of_fin 8600 200 complete_chunk43

lemma complete_chunk44 : ∀ i : Fin 200, Compatible (8800 + i.val) →
    (table.lookup (8800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk44 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 8800 9000 :=
  FiniteIntervals.of_fin 8800 200 complete_chunk44

lemma complete_chunk45 : ∀ i : Fin 200, Compatible (9000 + i.val) →
    (table.lookup (9000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk45 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 9000 9200 :=
  FiniteIntervals.of_fin 9000 200 complete_chunk45

lemma complete_chunk46 : ∀ i : Fin 200, Compatible (9200 + i.val) →
    (table.lookup (9200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk46 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 9200 9400 :=
  FiniteIntervals.of_fin 9200 200 complete_chunk46

lemma complete_chunk47 : ∀ i : Fin 200, Compatible (9400 + i.val) →
    (table.lookup (9400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk47 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 9400 9600 :=
  FiniteIntervals.of_fin 9400 200 complete_chunk47

lemma complete_chunk48 : ∀ i : Fin 200, Compatible (9600 + i.val) →
    (table.lookup (9600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk48 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 9600 9800 :=
  FiniteIntervals.of_fin 9600 200 complete_chunk48

lemma complete_chunk49 : ∀ i : Fin 200, Compatible (9800 + i.val) →
    (table.lookup (9800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk49 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 9800 10000 :=
  FiniteIntervals.of_fin 9800 200 complete_chunk49

#print axioms interval_chunk40
end Erdos184Work.PureFiveFilter3
