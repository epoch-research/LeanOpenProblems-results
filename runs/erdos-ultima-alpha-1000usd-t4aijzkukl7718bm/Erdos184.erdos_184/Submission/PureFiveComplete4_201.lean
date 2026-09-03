import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2010 : ∀ i : Fin 200, Compatible (402000 + i.val) →
    (table.lookup (402000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2010 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 402000 402200 :=
  FiniteIntervals.of_fin 402000 200 complete_chunk2010

lemma complete_chunk2011 : ∀ i : Fin 200, Compatible (402200 + i.val) →
    (table.lookup (402200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2011 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 402200 402400 :=
  FiniteIntervals.of_fin 402200 200 complete_chunk2011

lemma complete_chunk2012 : ∀ i : Fin 200, Compatible (402400 + i.val) →
    (table.lookup (402400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2012 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 402400 402600 :=
  FiniteIntervals.of_fin 402400 200 complete_chunk2012

lemma complete_chunk2013 : ∀ i : Fin 200, Compatible (402600 + i.val) →
    (table.lookup (402600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2013 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 402600 402800 :=
  FiniteIntervals.of_fin 402600 200 complete_chunk2013

lemma complete_chunk2014 : ∀ i : Fin 200, Compatible (402800 + i.val) →
    (table.lookup (402800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2014 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 402800 403000 :=
  FiniteIntervals.of_fin 402800 200 complete_chunk2014

lemma complete_chunk2015 : ∀ i : Fin 200, Compatible (403000 + i.val) →
    (table.lookup (403000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2015 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 403000 403200 :=
  FiniteIntervals.of_fin 403000 200 complete_chunk2015

lemma complete_chunk2016 : ∀ i : Fin 200, Compatible (403200 + i.val) →
    (table.lookup (403200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2016 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 403200 403400 :=
  FiniteIntervals.of_fin 403200 200 complete_chunk2016

lemma complete_chunk2017 : ∀ i : Fin 200, Compatible (403400 + i.val) →
    (table.lookup (403400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2017 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 403400 403600 :=
  FiniteIntervals.of_fin 403400 200 complete_chunk2017

lemma complete_chunk2018 : ∀ i : Fin 200, Compatible (403600 + i.val) →
    (table.lookup (403600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2018 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 403600 403800 :=
  FiniteIntervals.of_fin 403600 200 complete_chunk2018

lemma complete_chunk2019 : ∀ i : Fin 200, Compatible (403800 + i.val) →
    (table.lookup (403800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2019 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 403800 404000 :=
  FiniteIntervals.of_fin 403800 200 complete_chunk2019

#print axioms interval_chunk2010
end Erdos184Work.PureFiveFilter4
