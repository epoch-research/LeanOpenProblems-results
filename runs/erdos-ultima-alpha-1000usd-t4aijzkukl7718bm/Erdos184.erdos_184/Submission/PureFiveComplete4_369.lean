import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3690 : ∀ i : Fin 200, Compatible (738000 + i.val) →
    (table.lookup (738000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3690 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 738000 738200 :=
  FiniteIntervals.of_fin 738000 200 complete_chunk3690

lemma complete_chunk3691 : ∀ i : Fin 200, Compatible (738200 + i.val) →
    (table.lookup (738200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3691 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 738200 738400 :=
  FiniteIntervals.of_fin 738200 200 complete_chunk3691

lemma complete_chunk3692 : ∀ i : Fin 200, Compatible (738400 + i.val) →
    (table.lookup (738400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3692 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 738400 738600 :=
  FiniteIntervals.of_fin 738400 200 complete_chunk3692

lemma complete_chunk3693 : ∀ i : Fin 200, Compatible (738600 + i.val) →
    (table.lookup (738600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3693 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 738600 738800 :=
  FiniteIntervals.of_fin 738600 200 complete_chunk3693

lemma complete_chunk3694 : ∀ i : Fin 200, Compatible (738800 + i.val) →
    (table.lookup (738800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3694 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 738800 739000 :=
  FiniteIntervals.of_fin 738800 200 complete_chunk3694

lemma complete_chunk3695 : ∀ i : Fin 200, Compatible (739000 + i.val) →
    (table.lookup (739000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3695 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 739000 739200 :=
  FiniteIntervals.of_fin 739000 200 complete_chunk3695

lemma complete_chunk3696 : ∀ i : Fin 200, Compatible (739200 + i.val) →
    (table.lookup (739200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3696 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 739200 739400 :=
  FiniteIntervals.of_fin 739200 200 complete_chunk3696

lemma complete_chunk3697 : ∀ i : Fin 200, Compatible (739400 + i.val) →
    (table.lookup (739400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3697 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 739400 739600 :=
  FiniteIntervals.of_fin 739400 200 complete_chunk3697

lemma complete_chunk3698 : ∀ i : Fin 200, Compatible (739600 + i.val) →
    (table.lookup (739600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3698 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 739600 739800 :=
  FiniteIntervals.of_fin 739600 200 complete_chunk3698

lemma complete_chunk3699 : ∀ i : Fin 200, Compatible (739800 + i.val) →
    (table.lookup (739800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3699 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 739800 740000 :=
  FiniteIntervals.of_fin 739800 200 complete_chunk3699

#print axioms interval_chunk3690
end Erdos184Work.PureFiveFilter4
