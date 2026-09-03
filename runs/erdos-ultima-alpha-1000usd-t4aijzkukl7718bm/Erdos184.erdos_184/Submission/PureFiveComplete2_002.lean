import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk20 : ∀ i : Fin 1000, Compatible (20000 + i.val) →
    (table.lookup (20000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk20 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 20000 21000 :=
  FiniteIntervals.of_fin 20000 1000 complete_chunk20

lemma complete_chunk21 : ∀ i : Fin 1000, Compatible (21000 + i.val) →
    (table.lookup (21000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk21 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 21000 22000 :=
  FiniteIntervals.of_fin 21000 1000 complete_chunk21

lemma complete_chunk22 : ∀ i : Fin 1000, Compatible (22000 + i.val) →
    (table.lookup (22000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk22 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 22000 23000 :=
  FiniteIntervals.of_fin 22000 1000 complete_chunk22

lemma complete_chunk23 : ∀ i : Fin 1000, Compatible (23000 + i.val) →
    (table.lookup (23000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk23 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 23000 24000 :=
  FiniteIntervals.of_fin 23000 1000 complete_chunk23

lemma complete_chunk24 : ∀ i : Fin 1000, Compatible (24000 + i.val) →
    (table.lookup (24000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk24 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 24000 25000 :=
  FiniteIntervals.of_fin 24000 1000 complete_chunk24

lemma complete_chunk25 : ∀ i : Fin 1000, Compatible (25000 + i.val) →
    (table.lookup (25000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk25 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 25000 26000 :=
  FiniteIntervals.of_fin 25000 1000 complete_chunk25

lemma complete_chunk26 : ∀ i : Fin 1000, Compatible (26000 + i.val) →
    (table.lookup (26000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk26 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 26000 27000 :=
  FiniteIntervals.of_fin 26000 1000 complete_chunk26

lemma complete_chunk27 : ∀ i : Fin 1000, Compatible (27000 + i.val) →
    (table.lookup (27000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk27 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 27000 28000 :=
  FiniteIntervals.of_fin 27000 1000 complete_chunk27

lemma complete_chunk28 : ∀ i : Fin 1000, Compatible (28000 + i.val) →
    (table.lookup (28000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk28 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 28000 29000 :=
  FiniteIntervals.of_fin 28000 1000 complete_chunk28

lemma complete_chunk29 : ∀ i : Fin 1000, Compatible (29000 + i.val) →
    (table.lookup (29000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk29 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 29000 30000 :=
  FiniteIntervals.of_fin 29000 1000 complete_chunk29

#print axioms interval_chunk20
end Erdos184Work.PureFiveFilter2
