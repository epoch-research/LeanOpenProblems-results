import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk30 : ∀ i : Fin 200, Compatible (6000 + i.val) →
    (table.lookup (6000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk30 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 6000 6200 :=
  FiniteIntervals.of_fin 6000 200 complete_chunk30

lemma complete_chunk31 : ∀ i : Fin 200, Compatible (6200 + i.val) →
    (table.lookup (6200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk31 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 6200 6400 :=
  FiniteIntervals.of_fin 6200 200 complete_chunk31

lemma complete_chunk32 : ∀ i : Fin 200, Compatible (6400 + i.val) →
    (table.lookup (6400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk32 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 6400 6600 :=
  FiniteIntervals.of_fin 6400 200 complete_chunk32

lemma complete_chunk33 : ∀ i : Fin 200, Compatible (6600 + i.val) →
    (table.lookup (6600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk33 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 6600 6800 :=
  FiniteIntervals.of_fin 6600 200 complete_chunk33

lemma complete_chunk34 : ∀ i : Fin 200, Compatible (6800 + i.val) →
    (table.lookup (6800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk34 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 6800 7000 :=
  FiniteIntervals.of_fin 6800 200 complete_chunk34

lemma complete_chunk35 : ∀ i : Fin 200, Compatible (7000 + i.val) →
    (table.lookup (7000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk35 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 7000 7200 :=
  FiniteIntervals.of_fin 7000 200 complete_chunk35

lemma complete_chunk36 : ∀ i : Fin 200, Compatible (7200 + i.val) →
    (table.lookup (7200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk36 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 7200 7400 :=
  FiniteIntervals.of_fin 7200 200 complete_chunk36

lemma complete_chunk37 : ∀ i : Fin 200, Compatible (7400 + i.val) →
    (table.lookup (7400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk37 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 7400 7600 :=
  FiniteIntervals.of_fin 7400 200 complete_chunk37

lemma complete_chunk38 : ∀ i : Fin 200, Compatible (7600 + i.val) →
    (table.lookup (7600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk38 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 7600 7800 :=
  FiniteIntervals.of_fin 7600 200 complete_chunk38

lemma complete_chunk39 : ∀ i : Fin 200, Compatible (7800 + i.val) →
    (table.lookup (7800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk39 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 7800 8000 :=
  FiniteIntervals.of_fin 7800 200 complete_chunk39

#print axioms interval_chunk30
end Erdos184Work.PureFiveFilter3
