import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4010 : ∀ i : Fin 200, Compatible (802000 + i.val) →
    (table.lookup (802000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4010 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 802000 802200 :=
  FiniteIntervals.of_fin 802000 200 complete_chunk4010

lemma complete_chunk4011 : ∀ i : Fin 200, Compatible (802200 + i.val) →
    (table.lookup (802200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4011 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 802200 802400 :=
  FiniteIntervals.of_fin 802200 200 complete_chunk4011

lemma complete_chunk4012 : ∀ i : Fin 200, Compatible (802400 + i.val) →
    (table.lookup (802400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4012 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 802400 802600 :=
  FiniteIntervals.of_fin 802400 200 complete_chunk4012

lemma complete_chunk4013 : ∀ i : Fin 200, Compatible (802600 + i.val) →
    (table.lookup (802600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4013 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 802600 802800 :=
  FiniteIntervals.of_fin 802600 200 complete_chunk4013

lemma complete_chunk4014 : ∀ i : Fin 200, Compatible (802800 + i.val) →
    (table.lookup (802800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4014 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 802800 803000 :=
  FiniteIntervals.of_fin 802800 200 complete_chunk4014

lemma complete_chunk4015 : ∀ i : Fin 200, Compatible (803000 + i.val) →
    (table.lookup (803000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4015 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 803000 803200 :=
  FiniteIntervals.of_fin 803000 200 complete_chunk4015

lemma complete_chunk4016 : ∀ i : Fin 200, Compatible (803200 + i.val) →
    (table.lookup (803200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4016 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 803200 803400 :=
  FiniteIntervals.of_fin 803200 200 complete_chunk4016

lemma complete_chunk4017 : ∀ i : Fin 200, Compatible (803400 + i.val) →
    (table.lookup (803400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4017 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 803400 803600 :=
  FiniteIntervals.of_fin 803400 200 complete_chunk4017

lemma complete_chunk4018 : ∀ i : Fin 200, Compatible (803600 + i.val) →
    (table.lookup (803600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4018 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 803600 803800 :=
  FiniteIntervals.of_fin 803600 200 complete_chunk4018

lemma complete_chunk4019 : ∀ i : Fin 200, Compatible (803800 + i.val) →
    (table.lookup (803800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4019 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 803800 804000 :=
  FiniteIntervals.of_fin 803800 200 complete_chunk4019

#print axioms interval_chunk4010
end Erdos184Work.PureFiveFilter4
