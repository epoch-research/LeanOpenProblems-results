import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3010 : ∀ i : Fin 200, Compatible (602000 + i.val) →
    (table.lookup (602000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3010 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 602000 602200 :=
  FiniteIntervals.of_fin 602000 200 complete_chunk3010

lemma complete_chunk3011 : ∀ i : Fin 200, Compatible (602200 + i.val) →
    (table.lookup (602200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3011 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 602200 602400 :=
  FiniteIntervals.of_fin 602200 200 complete_chunk3011

lemma complete_chunk3012 : ∀ i : Fin 200, Compatible (602400 + i.val) →
    (table.lookup (602400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3012 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 602400 602600 :=
  FiniteIntervals.of_fin 602400 200 complete_chunk3012

lemma complete_chunk3013 : ∀ i : Fin 200, Compatible (602600 + i.val) →
    (table.lookup (602600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3013 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 602600 602800 :=
  FiniteIntervals.of_fin 602600 200 complete_chunk3013

lemma complete_chunk3014 : ∀ i : Fin 200, Compatible (602800 + i.val) →
    (table.lookup (602800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3014 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 602800 603000 :=
  FiniteIntervals.of_fin 602800 200 complete_chunk3014

lemma complete_chunk3015 : ∀ i : Fin 200, Compatible (603000 + i.val) →
    (table.lookup (603000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3015 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 603000 603200 :=
  FiniteIntervals.of_fin 603000 200 complete_chunk3015

lemma complete_chunk3016 : ∀ i : Fin 200, Compatible (603200 + i.val) →
    (table.lookup (603200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3016 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 603200 603400 :=
  FiniteIntervals.of_fin 603200 200 complete_chunk3016

lemma complete_chunk3017 : ∀ i : Fin 200, Compatible (603400 + i.val) →
    (table.lookup (603400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3017 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 603400 603600 :=
  FiniteIntervals.of_fin 603400 200 complete_chunk3017

lemma complete_chunk3018 : ∀ i : Fin 200, Compatible (603600 + i.val) →
    (table.lookup (603600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3018 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 603600 603800 :=
  FiniteIntervals.of_fin 603600 200 complete_chunk3018

lemma complete_chunk3019 : ∀ i : Fin 200, Compatible (603800 + i.val) →
    (table.lookup (603800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3019 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 603800 604000 :=
  FiniteIntervals.of_fin 603800 200 complete_chunk3019

#print axioms interval_chunk3010
end Erdos184Work.PureFiveFilter4
