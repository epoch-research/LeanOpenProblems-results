import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4770 : ∀ i : Fin 200, Compatible (954000 + i.val) →
    (table.lookup (954000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4770 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 954000 954200 :=
  FiniteIntervals.of_fin 954000 200 complete_chunk4770

lemma complete_chunk4771 : ∀ i : Fin 200, Compatible (954200 + i.val) →
    (table.lookup (954200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4771 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 954200 954400 :=
  FiniteIntervals.of_fin 954200 200 complete_chunk4771

lemma complete_chunk4772 : ∀ i : Fin 200, Compatible (954400 + i.val) →
    (table.lookup (954400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4772 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 954400 954600 :=
  FiniteIntervals.of_fin 954400 200 complete_chunk4772

lemma complete_chunk4773 : ∀ i : Fin 200, Compatible (954600 + i.val) →
    (table.lookup (954600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4773 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 954600 954800 :=
  FiniteIntervals.of_fin 954600 200 complete_chunk4773

lemma complete_chunk4774 : ∀ i : Fin 200, Compatible (954800 + i.val) →
    (table.lookup (954800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4774 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 954800 955000 :=
  FiniteIntervals.of_fin 954800 200 complete_chunk4774

lemma complete_chunk4775 : ∀ i : Fin 200, Compatible (955000 + i.val) →
    (table.lookup (955000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4775 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 955000 955200 :=
  FiniteIntervals.of_fin 955000 200 complete_chunk4775

lemma complete_chunk4776 : ∀ i : Fin 200, Compatible (955200 + i.val) →
    (table.lookup (955200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4776 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 955200 955400 :=
  FiniteIntervals.of_fin 955200 200 complete_chunk4776

lemma complete_chunk4777 : ∀ i : Fin 200, Compatible (955400 + i.val) →
    (table.lookup (955400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4777 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 955400 955600 :=
  FiniteIntervals.of_fin 955400 200 complete_chunk4777

lemma complete_chunk4778 : ∀ i : Fin 200, Compatible (955600 + i.val) →
    (table.lookup (955600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4778 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 955600 955800 :=
  FiniteIntervals.of_fin 955600 200 complete_chunk4778

lemma complete_chunk4779 : ∀ i : Fin 200, Compatible (955800 + i.val) →
    (table.lookup (955800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4779 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 955800 956000 :=
  FiniteIntervals.of_fin 955800 200 complete_chunk4779

#print axioms interval_chunk4770
end Erdos184Work.PureFiveFilter4
