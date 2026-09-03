import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4710 : ∀ i : Fin 200, Compatible (942000 + i.val) →
    (table.lookup (942000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4710 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 942000 942200 :=
  FiniteIntervals.of_fin 942000 200 complete_chunk4710

lemma complete_chunk4711 : ∀ i : Fin 200, Compatible (942200 + i.val) →
    (table.lookup (942200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4711 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 942200 942400 :=
  FiniteIntervals.of_fin 942200 200 complete_chunk4711

lemma complete_chunk4712 : ∀ i : Fin 200, Compatible (942400 + i.val) →
    (table.lookup (942400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4712 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 942400 942600 :=
  FiniteIntervals.of_fin 942400 200 complete_chunk4712

lemma complete_chunk4713 : ∀ i : Fin 200, Compatible (942600 + i.val) →
    (table.lookup (942600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4713 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 942600 942800 :=
  FiniteIntervals.of_fin 942600 200 complete_chunk4713

lemma complete_chunk4714 : ∀ i : Fin 200, Compatible (942800 + i.val) →
    (table.lookup (942800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4714 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 942800 943000 :=
  FiniteIntervals.of_fin 942800 200 complete_chunk4714

lemma complete_chunk4715 : ∀ i : Fin 200, Compatible (943000 + i.val) →
    (table.lookup (943000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4715 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 943000 943200 :=
  FiniteIntervals.of_fin 943000 200 complete_chunk4715

lemma complete_chunk4716 : ∀ i : Fin 200, Compatible (943200 + i.val) →
    (table.lookup (943200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4716 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 943200 943400 :=
  FiniteIntervals.of_fin 943200 200 complete_chunk4716

lemma complete_chunk4717 : ∀ i : Fin 200, Compatible (943400 + i.val) →
    (table.lookup (943400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4717 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 943400 943600 :=
  FiniteIntervals.of_fin 943400 200 complete_chunk4717

lemma complete_chunk4718 : ∀ i : Fin 200, Compatible (943600 + i.val) →
    (table.lookup (943600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4718 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 943600 943800 :=
  FiniteIntervals.of_fin 943600 200 complete_chunk4718

lemma complete_chunk4719 : ∀ i : Fin 200, Compatible (943800 + i.val) →
    (table.lookup (943800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4719 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 943800 944000 :=
  FiniteIntervals.of_fin 943800 200 complete_chunk4719

#print axioms interval_chunk4710
end Erdos184Work.PureFiveFilter4
