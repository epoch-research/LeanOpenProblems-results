import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk80 : ∀ i : Fin 200, Compatible (16000 + i.val) →
    (table.lookup (16000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk80 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 16000 16200 :=
  FiniteIntervals.of_fin 16000 200 complete_chunk80

lemma complete_chunk81 : ∀ i : Fin 200, Compatible (16200 + i.val) →
    (table.lookup (16200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk81 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 16200 16400 :=
  FiniteIntervals.of_fin 16200 200 complete_chunk81

lemma complete_chunk82 : ∀ i : Fin 200, Compatible (16400 + i.val) →
    (table.lookup (16400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk82 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 16400 16600 :=
  FiniteIntervals.of_fin 16400 200 complete_chunk82

lemma complete_chunk83 : ∀ i : Fin 200, Compatible (16600 + i.val) →
    (table.lookup (16600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk83 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 16600 16800 :=
  FiniteIntervals.of_fin 16600 200 complete_chunk83

lemma complete_chunk84 : ∀ i : Fin 200, Compatible (16800 + i.val) →
    (table.lookup (16800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk84 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 16800 17000 :=
  FiniteIntervals.of_fin 16800 200 complete_chunk84

lemma complete_chunk85 : ∀ i : Fin 200, Compatible (17000 + i.val) →
    (table.lookup (17000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk85 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 17000 17200 :=
  FiniteIntervals.of_fin 17000 200 complete_chunk85

lemma complete_chunk86 : ∀ i : Fin 200, Compatible (17200 + i.val) →
    (table.lookup (17200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk86 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 17200 17400 :=
  FiniteIntervals.of_fin 17200 200 complete_chunk86

lemma complete_chunk87 : ∀ i : Fin 200, Compatible (17400 + i.val) →
    (table.lookup (17400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk87 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 17400 17600 :=
  FiniteIntervals.of_fin 17400 200 complete_chunk87

lemma complete_chunk88 : ∀ i : Fin 200, Compatible (17600 + i.val) →
    (table.lookup (17600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk88 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 17600 17800 :=
  FiniteIntervals.of_fin 17600 200 complete_chunk88

lemma complete_chunk89 : ∀ i : Fin 200, Compatible (17800 + i.val) →
    (table.lookup (17800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk89 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 17800 18000 :=
  FiniteIntervals.of_fin 17800 200 complete_chunk89

#print axioms interval_chunk80
end Erdos184Work.PureFiveFilter3
