import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4780 : ∀ i : Fin 200, Compatible (956000 + i.val) →
    (table.lookup (956000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4780 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 956000 956200 :=
  FiniteIntervals.of_fin 956000 200 complete_chunk4780

lemma complete_chunk4781 : ∀ i : Fin 200, Compatible (956200 + i.val) →
    (table.lookup (956200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4781 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 956200 956400 :=
  FiniteIntervals.of_fin 956200 200 complete_chunk4781

lemma complete_chunk4782 : ∀ i : Fin 200, Compatible (956400 + i.val) →
    (table.lookup (956400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4782 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 956400 956600 :=
  FiniteIntervals.of_fin 956400 200 complete_chunk4782

lemma complete_chunk4783 : ∀ i : Fin 200, Compatible (956600 + i.val) →
    (table.lookup (956600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4783 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 956600 956800 :=
  FiniteIntervals.of_fin 956600 200 complete_chunk4783

lemma complete_chunk4784 : ∀ i : Fin 200, Compatible (956800 + i.val) →
    (table.lookup (956800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4784 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 956800 957000 :=
  FiniteIntervals.of_fin 956800 200 complete_chunk4784

lemma complete_chunk4785 : ∀ i : Fin 200, Compatible (957000 + i.val) →
    (table.lookup (957000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4785 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 957000 957200 :=
  FiniteIntervals.of_fin 957000 200 complete_chunk4785

lemma complete_chunk4786 : ∀ i : Fin 200, Compatible (957200 + i.val) →
    (table.lookup (957200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4786 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 957200 957400 :=
  FiniteIntervals.of_fin 957200 200 complete_chunk4786

lemma complete_chunk4787 : ∀ i : Fin 200, Compatible (957400 + i.val) →
    (table.lookup (957400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4787 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 957400 957600 :=
  FiniteIntervals.of_fin 957400 200 complete_chunk4787

lemma complete_chunk4788 : ∀ i : Fin 200, Compatible (957600 + i.val) →
    (table.lookup (957600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4788 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 957600 957800 :=
  FiniteIntervals.of_fin 957600 200 complete_chunk4788

lemma complete_chunk4789 : ∀ i : Fin 200, Compatible (957800 + i.val) →
    (table.lookup (957800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4789 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 957800 958000 :=
  FiniteIntervals.of_fin 957800 200 complete_chunk4789

#print axioms interval_chunk4780
end Erdos184Work.PureFiveFilter4
