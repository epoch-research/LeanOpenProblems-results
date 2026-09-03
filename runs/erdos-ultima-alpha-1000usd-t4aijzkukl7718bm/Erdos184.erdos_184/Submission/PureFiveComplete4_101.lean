import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1010 : ∀ i : Fin 200, Compatible (202000 + i.val) →
    (table.lookup (202000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1010 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 202000 202200 :=
  FiniteIntervals.of_fin 202000 200 complete_chunk1010

lemma complete_chunk1011 : ∀ i : Fin 200, Compatible (202200 + i.val) →
    (table.lookup (202200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1011 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 202200 202400 :=
  FiniteIntervals.of_fin 202200 200 complete_chunk1011

lemma complete_chunk1012 : ∀ i : Fin 200, Compatible (202400 + i.val) →
    (table.lookup (202400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1012 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 202400 202600 :=
  FiniteIntervals.of_fin 202400 200 complete_chunk1012

lemma complete_chunk1013 : ∀ i : Fin 200, Compatible (202600 + i.val) →
    (table.lookup (202600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1013 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 202600 202800 :=
  FiniteIntervals.of_fin 202600 200 complete_chunk1013

lemma complete_chunk1014 : ∀ i : Fin 200, Compatible (202800 + i.val) →
    (table.lookup (202800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1014 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 202800 203000 :=
  FiniteIntervals.of_fin 202800 200 complete_chunk1014

lemma complete_chunk1015 : ∀ i : Fin 200, Compatible (203000 + i.val) →
    (table.lookup (203000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1015 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 203000 203200 :=
  FiniteIntervals.of_fin 203000 200 complete_chunk1015

lemma complete_chunk1016 : ∀ i : Fin 200, Compatible (203200 + i.val) →
    (table.lookup (203200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1016 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 203200 203400 :=
  FiniteIntervals.of_fin 203200 200 complete_chunk1016

lemma complete_chunk1017 : ∀ i : Fin 200, Compatible (203400 + i.val) →
    (table.lookup (203400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1017 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 203400 203600 :=
  FiniteIntervals.of_fin 203400 200 complete_chunk1017

lemma complete_chunk1018 : ∀ i : Fin 200, Compatible (203600 + i.val) →
    (table.lookup (203600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1018 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 203600 203800 :=
  FiniteIntervals.of_fin 203600 200 complete_chunk1018

lemma complete_chunk1019 : ∀ i : Fin 200, Compatible (203800 + i.val) →
    (table.lookup (203800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1019 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 203800 204000 :=
  FiniteIntervals.of_fin 203800 200 complete_chunk1019

#print axioms interval_chunk1010
end Erdos184Work.PureFiveFilter4
