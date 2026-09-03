import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5010 : ∀ i : Fin 200, Compatible (1002000 + i.val) →
    (table.lookup (1002000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5010 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1002000 1002200 :=
  FiniteIntervals.of_fin 1002000 200 complete_chunk5010

lemma complete_chunk5011 : ∀ i : Fin 200, Compatible (1002200 + i.val) →
    (table.lookup (1002200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5011 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1002200 1002400 :=
  FiniteIntervals.of_fin 1002200 200 complete_chunk5011

lemma complete_chunk5012 : ∀ i : Fin 200, Compatible (1002400 + i.val) →
    (table.lookup (1002400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5012 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1002400 1002600 :=
  FiniteIntervals.of_fin 1002400 200 complete_chunk5012

lemma complete_chunk5013 : ∀ i : Fin 200, Compatible (1002600 + i.val) →
    (table.lookup (1002600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5013 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1002600 1002800 :=
  FiniteIntervals.of_fin 1002600 200 complete_chunk5013

lemma complete_chunk5014 : ∀ i : Fin 200, Compatible (1002800 + i.val) →
    (table.lookup (1002800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5014 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1002800 1003000 :=
  FiniteIntervals.of_fin 1002800 200 complete_chunk5014

lemma complete_chunk5015 : ∀ i : Fin 200, Compatible (1003000 + i.val) →
    (table.lookup (1003000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5015 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1003000 1003200 :=
  FiniteIntervals.of_fin 1003000 200 complete_chunk5015

lemma complete_chunk5016 : ∀ i : Fin 200, Compatible (1003200 + i.val) →
    (table.lookup (1003200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5016 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1003200 1003400 :=
  FiniteIntervals.of_fin 1003200 200 complete_chunk5016

lemma complete_chunk5017 : ∀ i : Fin 200, Compatible (1003400 + i.val) →
    (table.lookup (1003400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5017 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1003400 1003600 :=
  FiniteIntervals.of_fin 1003400 200 complete_chunk5017

lemma complete_chunk5018 : ∀ i : Fin 200, Compatible (1003600 + i.val) →
    (table.lookup (1003600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5018 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1003600 1003800 :=
  FiniteIntervals.of_fin 1003600 200 complete_chunk5018

lemma complete_chunk5019 : ∀ i : Fin 200, Compatible (1003800 + i.val) →
    (table.lookup (1003800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5019 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1003800 1004000 :=
  FiniteIntervals.of_fin 1003800 200 complete_chunk5019

#print axioms interval_chunk5010
end Erdos184Work.PureFiveFilter4
