import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk40 : ∀ i : Fin 1000, Compatible (40000 + i.val) →
    (table.lookup (40000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk40 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 40000 41000 :=
  FiniteIntervals.of_fin 40000 1000 complete_chunk40

lemma complete_chunk41 : ∀ i : Fin 1000, Compatible (41000 + i.val) →
    (table.lookup (41000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk41 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 41000 42000 :=
  FiniteIntervals.of_fin 41000 1000 complete_chunk41

lemma complete_chunk42 : ∀ i : Fin 1000, Compatible (42000 + i.val) →
    (table.lookup (42000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk42 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 42000 43000 :=
  FiniteIntervals.of_fin 42000 1000 complete_chunk42

lemma complete_chunk43 : ∀ i : Fin 1000, Compatible (43000 + i.val) →
    (table.lookup (43000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk43 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 43000 44000 :=
  FiniteIntervals.of_fin 43000 1000 complete_chunk43

lemma complete_chunk44 : ∀ i : Fin 1000, Compatible (44000 + i.val) →
    (table.lookup (44000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk44 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 44000 45000 :=
  FiniteIntervals.of_fin 44000 1000 complete_chunk44

lemma complete_chunk45 : ∀ i : Fin 1000, Compatible (45000 + i.val) →
    (table.lookup (45000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk45 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 45000 46000 :=
  FiniteIntervals.of_fin 45000 1000 complete_chunk45

lemma complete_chunk46 : ∀ i : Fin 1000, Compatible (46000 + i.val) →
    (table.lookup (46000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk46 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 46000 47000 :=
  FiniteIntervals.of_fin 46000 1000 complete_chunk46

lemma complete_chunk47 : ∀ i : Fin 1000, Compatible (47000 + i.val) →
    (table.lookup (47000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk47 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 47000 48000 :=
  FiniteIntervals.of_fin 47000 1000 complete_chunk47

lemma complete_chunk48 : ∀ i : Fin 1000, Compatible (48000 + i.val) →
    (table.lookup (48000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk48 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 48000 49000 :=
  FiniteIntervals.of_fin 48000 1000 complete_chunk48

lemma complete_chunk49 : ∀ i : Fin 1000, Compatible (49000 + i.val) →
    (table.lookup (49000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk49 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 49000 50000 :=
  FiniteIntervals.of_fin 49000 1000 complete_chunk49

#print axioms interval_chunk40
end Erdos184Work.PureFiveFilter2
