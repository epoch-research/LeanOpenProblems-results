import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk30 : ∀ i : Fin 1000, Compatible (30000 + i.val) →
    (table.lookup (30000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk30 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 30000 31000 :=
  FiniteIntervals.of_fin 30000 1000 complete_chunk30

lemma complete_chunk31 : ∀ i : Fin 1000, Compatible (31000 + i.val) →
    (table.lookup (31000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk31 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 31000 32000 :=
  FiniteIntervals.of_fin 31000 1000 complete_chunk31

lemma complete_chunk32 : ∀ i : Fin 1000, Compatible (32000 + i.val) →
    (table.lookup (32000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk32 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 32000 33000 :=
  FiniteIntervals.of_fin 32000 1000 complete_chunk32

lemma complete_chunk33 : ∀ i : Fin 1000, Compatible (33000 + i.val) →
    (table.lookup (33000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk33 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 33000 34000 :=
  FiniteIntervals.of_fin 33000 1000 complete_chunk33

lemma complete_chunk34 : ∀ i : Fin 1000, Compatible (34000 + i.val) →
    (table.lookup (34000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk34 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 34000 35000 :=
  FiniteIntervals.of_fin 34000 1000 complete_chunk34

lemma complete_chunk35 : ∀ i : Fin 1000, Compatible (35000 + i.val) →
    (table.lookup (35000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk35 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 35000 36000 :=
  FiniteIntervals.of_fin 35000 1000 complete_chunk35

lemma complete_chunk36 : ∀ i : Fin 1000, Compatible (36000 + i.val) →
    (table.lookup (36000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk36 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 36000 37000 :=
  FiniteIntervals.of_fin 36000 1000 complete_chunk36

lemma complete_chunk37 : ∀ i : Fin 1000, Compatible (37000 + i.val) →
    (table.lookup (37000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk37 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 37000 38000 :=
  FiniteIntervals.of_fin 37000 1000 complete_chunk37

lemma complete_chunk38 : ∀ i : Fin 1000, Compatible (38000 + i.val) →
    (table.lookup (38000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk38 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 38000 39000 :=
  FiniteIntervals.of_fin 38000 1000 complete_chunk38

lemma complete_chunk39 : ∀ i : Fin 1000, Compatible (39000 + i.val) →
    (table.lookup (39000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk39 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 39000 40000 :=
  FiniteIntervals.of_fin 39000 1000 complete_chunk39

#print axioms interval_chunk30
end Erdos184Work.PureFiveFilter2
