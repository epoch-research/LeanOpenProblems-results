import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3770 : ∀ i : Fin 200, Compatible (754000 + i.val) →
    (table.lookup (754000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3770 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 754000 754200 :=
  FiniteIntervals.of_fin 754000 200 complete_chunk3770

lemma complete_chunk3771 : ∀ i : Fin 200, Compatible (754200 + i.val) →
    (table.lookup (754200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3771 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 754200 754400 :=
  FiniteIntervals.of_fin 754200 200 complete_chunk3771

lemma complete_chunk3772 : ∀ i : Fin 200, Compatible (754400 + i.val) →
    (table.lookup (754400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3772 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 754400 754600 :=
  FiniteIntervals.of_fin 754400 200 complete_chunk3772

lemma complete_chunk3773 : ∀ i : Fin 200, Compatible (754600 + i.val) →
    (table.lookup (754600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3773 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 754600 754800 :=
  FiniteIntervals.of_fin 754600 200 complete_chunk3773

lemma complete_chunk3774 : ∀ i : Fin 200, Compatible (754800 + i.val) →
    (table.lookup (754800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3774 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 754800 755000 :=
  FiniteIntervals.of_fin 754800 200 complete_chunk3774

lemma complete_chunk3775 : ∀ i : Fin 200, Compatible (755000 + i.val) →
    (table.lookup (755000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3775 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 755000 755200 :=
  FiniteIntervals.of_fin 755000 200 complete_chunk3775

lemma complete_chunk3776 : ∀ i : Fin 200, Compatible (755200 + i.val) →
    (table.lookup (755200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3776 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 755200 755400 :=
  FiniteIntervals.of_fin 755200 200 complete_chunk3776

lemma complete_chunk3777 : ∀ i : Fin 200, Compatible (755400 + i.val) →
    (table.lookup (755400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3777 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 755400 755600 :=
  FiniteIntervals.of_fin 755400 200 complete_chunk3777

lemma complete_chunk3778 : ∀ i : Fin 200, Compatible (755600 + i.val) →
    (table.lookup (755600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3778 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 755600 755800 :=
  FiniteIntervals.of_fin 755600 200 complete_chunk3778

lemma complete_chunk3779 : ∀ i : Fin 200, Compatible (755800 + i.val) →
    (table.lookup (755800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3779 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 755800 756000 :=
  FiniteIntervals.of_fin 755800 200 complete_chunk3779

#print axioms interval_chunk3770
end Erdos184Work.PureFiveFilter4
