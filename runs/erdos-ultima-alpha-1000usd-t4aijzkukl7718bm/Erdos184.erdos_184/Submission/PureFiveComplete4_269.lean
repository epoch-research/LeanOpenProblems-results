import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2690 : ∀ i : Fin 200, Compatible (538000 + i.val) →
    (table.lookup (538000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2690 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 538000 538200 :=
  FiniteIntervals.of_fin 538000 200 complete_chunk2690

lemma complete_chunk2691 : ∀ i : Fin 200, Compatible (538200 + i.val) →
    (table.lookup (538200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2691 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 538200 538400 :=
  FiniteIntervals.of_fin 538200 200 complete_chunk2691

lemma complete_chunk2692 : ∀ i : Fin 200, Compatible (538400 + i.val) →
    (table.lookup (538400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2692 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 538400 538600 :=
  FiniteIntervals.of_fin 538400 200 complete_chunk2692

lemma complete_chunk2693 : ∀ i : Fin 200, Compatible (538600 + i.val) →
    (table.lookup (538600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2693 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 538600 538800 :=
  FiniteIntervals.of_fin 538600 200 complete_chunk2693

lemma complete_chunk2694 : ∀ i : Fin 200, Compatible (538800 + i.val) →
    (table.lookup (538800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2694 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 538800 539000 :=
  FiniteIntervals.of_fin 538800 200 complete_chunk2694

lemma complete_chunk2695 : ∀ i : Fin 200, Compatible (539000 + i.val) →
    (table.lookup (539000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2695 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 539000 539200 :=
  FiniteIntervals.of_fin 539000 200 complete_chunk2695

lemma complete_chunk2696 : ∀ i : Fin 200, Compatible (539200 + i.val) →
    (table.lookup (539200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2696 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 539200 539400 :=
  FiniteIntervals.of_fin 539200 200 complete_chunk2696

lemma complete_chunk2697 : ∀ i : Fin 200, Compatible (539400 + i.val) →
    (table.lookup (539400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2697 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 539400 539600 :=
  FiniteIntervals.of_fin 539400 200 complete_chunk2697

lemma complete_chunk2698 : ∀ i : Fin 200, Compatible (539600 + i.val) →
    (table.lookup (539600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2698 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 539600 539800 :=
  FiniteIntervals.of_fin 539600 200 complete_chunk2698

lemma complete_chunk2699 : ∀ i : Fin 200, Compatible (539800 + i.val) →
    (table.lookup (539800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2699 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 539800 540000 :=
  FiniteIntervals.of_fin 539800 200 complete_chunk2699

#print axioms interval_chunk2690
end Erdos184Work.PureFiveFilter4
