import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk10 : ∀ i : Fin 200, Compatible (2000 + i.val) →
    (table.lookup (2000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk10 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 2000 2200 :=
  FiniteIntervals.of_fin 2000 200 complete_chunk10

lemma complete_chunk11 : ∀ i : Fin 200, Compatible (2200 + i.val) →
    (table.lookup (2200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk11 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 2200 2400 :=
  FiniteIntervals.of_fin 2200 200 complete_chunk11

lemma complete_chunk12 : ∀ i : Fin 200, Compatible (2400 + i.val) →
    (table.lookup (2400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk12 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 2400 2600 :=
  FiniteIntervals.of_fin 2400 200 complete_chunk12

lemma complete_chunk13 : ∀ i : Fin 200, Compatible (2600 + i.val) →
    (table.lookup (2600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk13 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 2600 2800 :=
  FiniteIntervals.of_fin 2600 200 complete_chunk13

lemma complete_chunk14 : ∀ i : Fin 200, Compatible (2800 + i.val) →
    (table.lookup (2800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk14 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 2800 3000 :=
  FiniteIntervals.of_fin 2800 200 complete_chunk14

lemma complete_chunk15 : ∀ i : Fin 200, Compatible (3000 + i.val) →
    (table.lookup (3000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk15 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3000 3200 :=
  FiniteIntervals.of_fin 3000 200 complete_chunk15

lemma complete_chunk16 : ∀ i : Fin 200, Compatible (3200 + i.val) →
    (table.lookup (3200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk16 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3200 3400 :=
  FiniteIntervals.of_fin 3200 200 complete_chunk16

lemma complete_chunk17 : ∀ i : Fin 200, Compatible (3400 + i.val) →
    (table.lookup (3400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk17 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3400 3600 :=
  FiniteIntervals.of_fin 3400 200 complete_chunk17

lemma complete_chunk18 : ∀ i : Fin 200, Compatible (3600 + i.val) →
    (table.lookup (3600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk18 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3600 3800 :=
  FiniteIntervals.of_fin 3600 200 complete_chunk18

lemma complete_chunk19 : ∀ i : Fin 200, Compatible (3800 + i.val) →
    (table.lookup (3800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk19 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 3800 4000 :=
  FiniteIntervals.of_fin 3800 200 complete_chunk19

#print axioms interval_chunk10
end Erdos184Work.PureFiveFilter3
