import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk770 : ∀ i : Fin 200, Compatible (154000 + i.val) →
    (table.lookup (154000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk770 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 154000 154200 :=
  FiniteIntervals.of_fin 154000 200 complete_chunk770

lemma complete_chunk771 : ∀ i : Fin 200, Compatible (154200 + i.val) →
    (table.lookup (154200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk771 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 154200 154400 :=
  FiniteIntervals.of_fin 154200 200 complete_chunk771

lemma complete_chunk772 : ∀ i : Fin 200, Compatible (154400 + i.val) →
    (table.lookup (154400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk772 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 154400 154600 :=
  FiniteIntervals.of_fin 154400 200 complete_chunk772

lemma complete_chunk773 : ∀ i : Fin 200, Compatible (154600 + i.val) →
    (table.lookup (154600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk773 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 154600 154800 :=
  FiniteIntervals.of_fin 154600 200 complete_chunk773

lemma complete_chunk774 : ∀ i : Fin 200, Compatible (154800 + i.val) →
    (table.lookup (154800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk774 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 154800 155000 :=
  FiniteIntervals.of_fin 154800 200 complete_chunk774

lemma complete_chunk775 : ∀ i : Fin 200, Compatible (155000 + i.val) →
    (table.lookup (155000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk775 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 155000 155200 :=
  FiniteIntervals.of_fin 155000 200 complete_chunk775

lemma complete_chunk776 : ∀ i : Fin 200, Compatible (155200 + i.val) →
    (table.lookup (155200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk776 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 155200 155400 :=
  FiniteIntervals.of_fin 155200 200 complete_chunk776

lemma complete_chunk777 : ∀ i : Fin 200, Compatible (155400 + i.val) →
    (table.lookup (155400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk777 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 155400 155600 :=
  FiniteIntervals.of_fin 155400 200 complete_chunk777

lemma complete_chunk778 : ∀ i : Fin 200, Compatible (155600 + i.val) →
    (table.lookup (155600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk778 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 155600 155800 :=
  FiniteIntervals.of_fin 155600 200 complete_chunk778

lemma complete_chunk779 : ∀ i : Fin 200, Compatible (155800 + i.val) →
    (table.lookup (155800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk779 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 155800 156000 :=
  FiniteIntervals.of_fin 155800 200 complete_chunk779

#print axioms interval_chunk770
end Erdos184Work.PureFiveFilter4
