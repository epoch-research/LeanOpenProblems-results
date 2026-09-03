import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4690 : ∀ i : Fin 200, Compatible (938000 + i.val) →
    (table.lookup (938000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4690 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 938000 938200 :=
  FiniteIntervals.of_fin 938000 200 complete_chunk4690

lemma complete_chunk4691 : ∀ i : Fin 200, Compatible (938200 + i.val) →
    (table.lookup (938200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4691 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 938200 938400 :=
  FiniteIntervals.of_fin 938200 200 complete_chunk4691

lemma complete_chunk4692 : ∀ i : Fin 200, Compatible (938400 + i.val) →
    (table.lookup (938400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4692 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 938400 938600 :=
  FiniteIntervals.of_fin 938400 200 complete_chunk4692

lemma complete_chunk4693 : ∀ i : Fin 200, Compatible (938600 + i.val) →
    (table.lookup (938600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4693 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 938600 938800 :=
  FiniteIntervals.of_fin 938600 200 complete_chunk4693

lemma complete_chunk4694 : ∀ i : Fin 200, Compatible (938800 + i.val) →
    (table.lookup (938800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4694 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 938800 939000 :=
  FiniteIntervals.of_fin 938800 200 complete_chunk4694

lemma complete_chunk4695 : ∀ i : Fin 200, Compatible (939000 + i.val) →
    (table.lookup (939000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4695 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 939000 939200 :=
  FiniteIntervals.of_fin 939000 200 complete_chunk4695

lemma complete_chunk4696 : ∀ i : Fin 200, Compatible (939200 + i.val) →
    (table.lookup (939200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4696 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 939200 939400 :=
  FiniteIntervals.of_fin 939200 200 complete_chunk4696

lemma complete_chunk4697 : ∀ i : Fin 200, Compatible (939400 + i.val) →
    (table.lookup (939400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4697 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 939400 939600 :=
  FiniteIntervals.of_fin 939400 200 complete_chunk4697

lemma complete_chunk4698 : ∀ i : Fin 200, Compatible (939600 + i.val) →
    (table.lookup (939600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4698 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 939600 939800 :=
  FiniteIntervals.of_fin 939600 200 complete_chunk4698

lemma complete_chunk4699 : ∀ i : Fin 200, Compatible (939800 + i.val) →
    (table.lookup (939800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4699 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 939800 940000 :=
  FiniteIntervals.of_fin 939800 200 complete_chunk4699

#print axioms interval_chunk4690
end Erdos184Work.PureFiveFilter4
