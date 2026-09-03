import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk20 : ∀ i : Fin 200, Compatible (4000 + i.val) →
    (table.lookup (4000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk20 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 4000 4200 :=
  FiniteIntervals.of_fin 4000 200 complete_chunk20

lemma complete_chunk21 : ∀ i : Fin 200, Compatible (4200 + i.val) →
    (table.lookup (4200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk21 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 4200 4400 :=
  FiniteIntervals.of_fin 4200 200 complete_chunk21

lemma complete_chunk22 : ∀ i : Fin 200, Compatible (4400 + i.val) →
    (table.lookup (4400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk22 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 4400 4600 :=
  FiniteIntervals.of_fin 4400 200 complete_chunk22

lemma complete_chunk23 : ∀ i : Fin 200, Compatible (4600 + i.val) →
    (table.lookup (4600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk23 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 4600 4800 :=
  FiniteIntervals.of_fin 4600 200 complete_chunk23

lemma complete_chunk24 : ∀ i : Fin 200, Compatible (4800 + i.val) →
    (table.lookup (4800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk24 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 4800 5000 :=
  FiniteIntervals.of_fin 4800 200 complete_chunk24

lemma complete_chunk25 : ∀ i : Fin 200, Compatible (5000 + i.val) →
    (table.lookup (5000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk25 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 5000 5200 :=
  FiniteIntervals.of_fin 5000 200 complete_chunk25

lemma complete_chunk26 : ∀ i : Fin 200, Compatible (5200 + i.val) →
    (table.lookup (5200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk26 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 5200 5400 :=
  FiniteIntervals.of_fin 5200 200 complete_chunk26

lemma complete_chunk27 : ∀ i : Fin 200, Compatible (5400 + i.val) →
    (table.lookup (5400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk27 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 5400 5600 :=
  FiniteIntervals.of_fin 5400 200 complete_chunk27

lemma complete_chunk28 : ∀ i : Fin 200, Compatible (5600 + i.val) →
    (table.lookup (5600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk28 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 5600 5800 :=
  FiniteIntervals.of_fin 5600 200 complete_chunk28

lemma complete_chunk29 : ∀ i : Fin 200, Compatible (5800 + i.val) →
    (table.lookup (5800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk29 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 5800 6000 :=
  FiniteIntervals.of_fin 5800 200 complete_chunk29

#print axioms interval_chunk20
end Erdos184Work.PureFiveFilter3
