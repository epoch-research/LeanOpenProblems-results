import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6010 : ∀ i : Fin 200, Compatible (1202000 + i.val) →
    (table.lookup (1202000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6010 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1202000 1202200 :=
  FiniteIntervals.of_fin 1202000 200 complete_chunk6010

lemma complete_chunk6011 : ∀ i : Fin 200, Compatible (1202200 + i.val) →
    (table.lookup (1202200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6011 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1202200 1202400 :=
  FiniteIntervals.of_fin 1202200 200 complete_chunk6011

lemma complete_chunk6012 : ∀ i : Fin 200, Compatible (1202400 + i.val) →
    (table.lookup (1202400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6012 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1202400 1202600 :=
  FiniteIntervals.of_fin 1202400 200 complete_chunk6012

lemma complete_chunk6013 : ∀ i : Fin 200, Compatible (1202600 + i.val) →
    (table.lookup (1202600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6013 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1202600 1202800 :=
  FiniteIntervals.of_fin 1202600 200 complete_chunk6013

lemma complete_chunk6014 : ∀ i : Fin 200, Compatible (1202800 + i.val) →
    (table.lookup (1202800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6014 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1202800 1203000 :=
  FiniteIntervals.of_fin 1202800 200 complete_chunk6014

lemma complete_chunk6015 : ∀ i : Fin 200, Compatible (1203000 + i.val) →
    (table.lookup (1203000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6015 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1203000 1203200 :=
  FiniteIntervals.of_fin 1203000 200 complete_chunk6015

lemma complete_chunk6016 : ∀ i : Fin 200, Compatible (1203200 + i.val) →
    (table.lookup (1203200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6016 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1203200 1203400 :=
  FiniteIntervals.of_fin 1203200 200 complete_chunk6016

lemma complete_chunk6017 : ∀ i : Fin 200, Compatible (1203400 + i.val) →
    (table.lookup (1203400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6017 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1203400 1203600 :=
  FiniteIntervals.of_fin 1203400 200 complete_chunk6017

lemma complete_chunk6018 : ∀ i : Fin 200, Compatible (1203600 + i.val) →
    (table.lookup (1203600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6018 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1203600 1203800 :=
  FiniteIntervals.of_fin 1203600 200 complete_chunk6018

lemma complete_chunk6019 : ∀ i : Fin 200, Compatible (1203800 + i.val) →
    (table.lookup (1203800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6019 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1203800 1204000 :=
  FiniteIntervals.of_fin 1203800 200 complete_chunk6019

#print axioms interval_chunk6010
end Erdos184Work.PureFiveFilter4
