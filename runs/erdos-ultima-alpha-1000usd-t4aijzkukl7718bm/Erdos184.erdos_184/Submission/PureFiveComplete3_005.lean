import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk50 : ∀ i : Fin 200, Compatible (10000 + i.val) →
    (table.lookup (10000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk50 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 10000 10200 :=
  FiniteIntervals.of_fin 10000 200 complete_chunk50

lemma complete_chunk51 : ∀ i : Fin 200, Compatible (10200 + i.val) →
    (table.lookup (10200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk51 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 10200 10400 :=
  FiniteIntervals.of_fin 10200 200 complete_chunk51

lemma complete_chunk52 : ∀ i : Fin 200, Compatible (10400 + i.val) →
    (table.lookup (10400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk52 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 10400 10600 :=
  FiniteIntervals.of_fin 10400 200 complete_chunk52

lemma complete_chunk53 : ∀ i : Fin 200, Compatible (10600 + i.val) →
    (table.lookup (10600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk53 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 10600 10800 :=
  FiniteIntervals.of_fin 10600 200 complete_chunk53

lemma complete_chunk54 : ∀ i : Fin 200, Compatible (10800 + i.val) →
    (table.lookup (10800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk54 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 10800 11000 :=
  FiniteIntervals.of_fin 10800 200 complete_chunk54

lemma complete_chunk55 : ∀ i : Fin 200, Compatible (11000 + i.val) →
    (table.lookup (11000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk55 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 11000 11200 :=
  FiniteIntervals.of_fin 11000 200 complete_chunk55

lemma complete_chunk56 : ∀ i : Fin 200, Compatible (11200 + i.val) →
    (table.lookup (11200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk56 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 11200 11400 :=
  FiniteIntervals.of_fin 11200 200 complete_chunk56

lemma complete_chunk57 : ∀ i : Fin 200, Compatible (11400 + i.val) →
    (table.lookup (11400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk57 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 11400 11600 :=
  FiniteIntervals.of_fin 11400 200 complete_chunk57

lemma complete_chunk58 : ∀ i : Fin 200, Compatible (11600 + i.val) →
    (table.lookup (11600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk58 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 11600 11800 :=
  FiniteIntervals.of_fin 11600 200 complete_chunk58

lemma complete_chunk59 : ∀ i : Fin 200, Compatible (11800 + i.val) →
    (table.lookup (11800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk59 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 11800 12000 :=
  FiniteIntervals.of_fin 11800 200 complete_chunk59

#print axioms interval_chunk50
end Erdos184Work.PureFiveFilter3
