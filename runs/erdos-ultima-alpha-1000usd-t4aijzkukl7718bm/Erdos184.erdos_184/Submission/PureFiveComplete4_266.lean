import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2660 : ∀ i : Fin 200, Compatible (532000 + i.val) →
    (table.lookup (532000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2660 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 532000 532200 :=
  FiniteIntervals.of_fin 532000 200 complete_chunk2660

lemma complete_chunk2661 : ∀ i : Fin 200, Compatible (532200 + i.val) →
    (table.lookup (532200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2661 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 532200 532400 :=
  FiniteIntervals.of_fin 532200 200 complete_chunk2661

lemma complete_chunk2662 : ∀ i : Fin 200, Compatible (532400 + i.val) →
    (table.lookup (532400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2662 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 532400 532600 :=
  FiniteIntervals.of_fin 532400 200 complete_chunk2662

lemma complete_chunk2663 : ∀ i : Fin 200, Compatible (532600 + i.val) →
    (table.lookup (532600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2663 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 532600 532800 :=
  FiniteIntervals.of_fin 532600 200 complete_chunk2663

lemma complete_chunk2664 : ∀ i : Fin 200, Compatible (532800 + i.val) →
    (table.lookup (532800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2664 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 532800 533000 :=
  FiniteIntervals.of_fin 532800 200 complete_chunk2664

lemma complete_chunk2665 : ∀ i : Fin 200, Compatible (533000 + i.val) →
    (table.lookup (533000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2665 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 533000 533200 :=
  FiniteIntervals.of_fin 533000 200 complete_chunk2665

lemma complete_chunk2666 : ∀ i : Fin 200, Compatible (533200 + i.val) →
    (table.lookup (533200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2666 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 533200 533400 :=
  FiniteIntervals.of_fin 533200 200 complete_chunk2666

lemma complete_chunk2667 : ∀ i : Fin 200, Compatible (533400 + i.val) →
    (table.lookup (533400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2667 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 533400 533600 :=
  FiniteIntervals.of_fin 533400 200 complete_chunk2667

lemma complete_chunk2668 : ∀ i : Fin 200, Compatible (533600 + i.val) →
    (table.lookup (533600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2668 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 533600 533800 :=
  FiniteIntervals.of_fin 533600 200 complete_chunk2668

lemma complete_chunk2669 : ∀ i : Fin 200, Compatible (533800 + i.val) →
    (table.lookup (533800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2669 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 533800 534000 :=
  FiniteIntervals.of_fin 533800 200 complete_chunk2669

#print axioms interval_chunk2660
end Erdos184Work.PureFiveFilter4
