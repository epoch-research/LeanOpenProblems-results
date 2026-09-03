import Submission.PureFiveFilter2
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter2
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk10 : ∀ i : Fin 1000, Compatible (10000 + i.val) →
    (table.lookup (10000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk10 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 10000 11000 :=
  FiniteIntervals.of_fin 10000 1000 complete_chunk10

lemma complete_chunk11 : ∀ i : Fin 1000, Compatible (11000 + i.val) →
    (table.lookup (11000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk11 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 11000 12000 :=
  FiniteIntervals.of_fin 11000 1000 complete_chunk11

lemma complete_chunk12 : ∀ i : Fin 1000, Compatible (12000 + i.val) →
    (table.lookup (12000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk12 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 12000 13000 :=
  FiniteIntervals.of_fin 12000 1000 complete_chunk12

lemma complete_chunk13 : ∀ i : Fin 1000, Compatible (13000 + i.val) →
    (table.lookup (13000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk13 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 13000 14000 :=
  FiniteIntervals.of_fin 13000 1000 complete_chunk13

lemma complete_chunk14 : ∀ i : Fin 1000, Compatible (14000 + i.val) →
    (table.lookup (14000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk14 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 14000 15000 :=
  FiniteIntervals.of_fin 14000 1000 complete_chunk14

lemma complete_chunk15 : ∀ i : Fin 1000, Compatible (15000 + i.val) →
    (table.lookup (15000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk15 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 15000 16000 :=
  FiniteIntervals.of_fin 15000 1000 complete_chunk15

lemma complete_chunk16 : ∀ i : Fin 1000, Compatible (16000 + i.val) →
    (table.lookup (16000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk16 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 16000 17000 :=
  FiniteIntervals.of_fin 16000 1000 complete_chunk16

lemma complete_chunk17 : ∀ i : Fin 1000, Compatible (17000 + i.val) →
    (table.lookup (17000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk17 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 17000 18000 :=
  FiniteIntervals.of_fin 17000 1000 complete_chunk17

lemma complete_chunk18 : ∀ i : Fin 1000, Compatible (18000 + i.val) →
    (table.lookup (18000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk18 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 18000 19000 :=
  FiniteIntervals.of_fin 18000 1000 complete_chunk18

lemma complete_chunk19 : ∀ i : Fin 1000, Compatible (19000 + i.val) →
    (table.lookup (19000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk19 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 19000 20000 :=
  FiniteIntervals.of_fin 19000 1000 complete_chunk19

#print axioms interval_chunk10
end Erdos184Work.PureFiveFilter2
