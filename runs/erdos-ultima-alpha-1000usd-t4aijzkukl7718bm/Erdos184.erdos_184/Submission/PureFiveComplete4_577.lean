import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5770 : ∀ i : Fin 200, Compatible (1154000 + i.val) →
    (table.lookup (1154000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5770 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1154000 1154200 :=
  FiniteIntervals.of_fin 1154000 200 complete_chunk5770

lemma complete_chunk5771 : ∀ i : Fin 200, Compatible (1154200 + i.val) →
    (table.lookup (1154200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5771 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1154200 1154400 :=
  FiniteIntervals.of_fin 1154200 200 complete_chunk5771

lemma complete_chunk5772 : ∀ i : Fin 200, Compatible (1154400 + i.val) →
    (table.lookup (1154400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5772 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1154400 1154600 :=
  FiniteIntervals.of_fin 1154400 200 complete_chunk5772

lemma complete_chunk5773 : ∀ i : Fin 200, Compatible (1154600 + i.val) →
    (table.lookup (1154600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5773 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1154600 1154800 :=
  FiniteIntervals.of_fin 1154600 200 complete_chunk5773

lemma complete_chunk5774 : ∀ i : Fin 200, Compatible (1154800 + i.val) →
    (table.lookup (1154800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5774 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1154800 1155000 :=
  FiniteIntervals.of_fin 1154800 200 complete_chunk5774

lemma complete_chunk5775 : ∀ i : Fin 200, Compatible (1155000 + i.val) →
    (table.lookup (1155000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5775 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1155000 1155200 :=
  FiniteIntervals.of_fin 1155000 200 complete_chunk5775

lemma complete_chunk5776 : ∀ i : Fin 200, Compatible (1155200 + i.val) →
    (table.lookup (1155200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5776 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1155200 1155400 :=
  FiniteIntervals.of_fin 1155200 200 complete_chunk5776

lemma complete_chunk5777 : ∀ i : Fin 200, Compatible (1155400 + i.val) →
    (table.lookup (1155400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5777 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1155400 1155600 :=
  FiniteIntervals.of_fin 1155400 200 complete_chunk5777

lemma complete_chunk5778 : ∀ i : Fin 200, Compatible (1155600 + i.val) →
    (table.lookup (1155600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5778 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1155600 1155800 :=
  FiniteIntervals.of_fin 1155600 200 complete_chunk5778

lemma complete_chunk5779 : ∀ i : Fin 200, Compatible (1155800 + i.val) →
    (table.lookup (1155800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5779 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1155800 1156000 :=
  FiniteIntervals.of_fin 1155800 200 complete_chunk5779

#print axioms interval_chunk5770
end Erdos184Work.PureFiveFilter4
