import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4760 : ∀ i : Fin 200, Compatible (952000 + i.val) →
    (table.lookup (952000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4760 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 952000 952200 :=
  FiniteIntervals.of_fin 952000 200 complete_chunk4760

lemma complete_chunk4761 : ∀ i : Fin 200, Compatible (952200 + i.val) →
    (table.lookup (952200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4761 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 952200 952400 :=
  FiniteIntervals.of_fin 952200 200 complete_chunk4761

lemma complete_chunk4762 : ∀ i : Fin 200, Compatible (952400 + i.val) →
    (table.lookup (952400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4762 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 952400 952600 :=
  FiniteIntervals.of_fin 952400 200 complete_chunk4762

lemma complete_chunk4763 : ∀ i : Fin 200, Compatible (952600 + i.val) →
    (table.lookup (952600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4763 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 952600 952800 :=
  FiniteIntervals.of_fin 952600 200 complete_chunk4763

lemma complete_chunk4764 : ∀ i : Fin 200, Compatible (952800 + i.val) →
    (table.lookup (952800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4764 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 952800 953000 :=
  FiniteIntervals.of_fin 952800 200 complete_chunk4764

lemma complete_chunk4765 : ∀ i : Fin 200, Compatible (953000 + i.val) →
    (table.lookup (953000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4765 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 953000 953200 :=
  FiniteIntervals.of_fin 953000 200 complete_chunk4765

lemma complete_chunk4766 : ∀ i : Fin 200, Compatible (953200 + i.val) →
    (table.lookup (953200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4766 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 953200 953400 :=
  FiniteIntervals.of_fin 953200 200 complete_chunk4766

lemma complete_chunk4767 : ∀ i : Fin 200, Compatible (953400 + i.val) →
    (table.lookup (953400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4767 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 953400 953600 :=
  FiniteIntervals.of_fin 953400 200 complete_chunk4767

lemma complete_chunk4768 : ∀ i : Fin 200, Compatible (953600 + i.val) →
    (table.lookup (953600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4768 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 953600 953800 :=
  FiniteIntervals.of_fin 953600 200 complete_chunk4768

lemma complete_chunk4769 : ∀ i : Fin 200, Compatible (953800 + i.val) →
    (table.lookup (953800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4769 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 953800 954000 :=
  FiniteIntervals.of_fin 953800 200 complete_chunk4769

#print axioms interval_chunk4760
end Erdos184Work.PureFiveFilter4
