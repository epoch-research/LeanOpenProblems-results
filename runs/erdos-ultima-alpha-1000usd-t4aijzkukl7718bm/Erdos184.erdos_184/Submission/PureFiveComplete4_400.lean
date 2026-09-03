import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4000 : ∀ i : Fin 200, Compatible (800000 + i.val) →
    (table.lookup (800000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4000 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 800000 800200 :=
  FiniteIntervals.of_fin 800000 200 complete_chunk4000

lemma complete_chunk4001 : ∀ i : Fin 200, Compatible (800200 + i.val) →
    (table.lookup (800200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4001 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 800200 800400 :=
  FiniteIntervals.of_fin 800200 200 complete_chunk4001

lemma complete_chunk4002 : ∀ i : Fin 200, Compatible (800400 + i.val) →
    (table.lookup (800400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4002 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 800400 800600 :=
  FiniteIntervals.of_fin 800400 200 complete_chunk4002

lemma complete_chunk4003 : ∀ i : Fin 200, Compatible (800600 + i.val) →
    (table.lookup (800600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4003 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 800600 800800 :=
  FiniteIntervals.of_fin 800600 200 complete_chunk4003

lemma complete_chunk4004 : ∀ i : Fin 200, Compatible (800800 + i.val) →
    (table.lookup (800800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4004 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 800800 801000 :=
  FiniteIntervals.of_fin 800800 200 complete_chunk4004

lemma complete_chunk4005 : ∀ i : Fin 200, Compatible (801000 + i.val) →
    (table.lookup (801000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4005 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 801000 801200 :=
  FiniteIntervals.of_fin 801000 200 complete_chunk4005

lemma complete_chunk4006 : ∀ i : Fin 200, Compatible (801200 + i.val) →
    (table.lookup (801200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4006 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 801200 801400 :=
  FiniteIntervals.of_fin 801200 200 complete_chunk4006

lemma complete_chunk4007 : ∀ i : Fin 200, Compatible (801400 + i.val) →
    (table.lookup (801400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4007 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 801400 801600 :=
  FiniteIntervals.of_fin 801400 200 complete_chunk4007

lemma complete_chunk4008 : ∀ i : Fin 200, Compatible (801600 + i.val) →
    (table.lookup (801600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4008 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 801600 801800 :=
  FiniteIntervals.of_fin 801600 200 complete_chunk4008

lemma complete_chunk4009 : ∀ i : Fin 200, Compatible (801800 + i.val) →
    (table.lookup (801800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4009 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 801800 802000 :=
  FiniteIntervals.of_fin 801800 200 complete_chunk4009

#print axioms interval_chunk4000
end Erdos184Work.PureFiveFilter4
