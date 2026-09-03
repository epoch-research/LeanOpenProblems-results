import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk780 : ∀ i : Fin 200, Compatible (156000 + i.val) →
    (table.lookup (156000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk780 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 156000 156200 :=
  FiniteIntervals.of_fin 156000 200 complete_chunk780

lemma complete_chunk781 : ∀ i : Fin 200, Compatible (156200 + i.val) →
    (table.lookup (156200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk781 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 156200 156400 :=
  FiniteIntervals.of_fin 156200 200 complete_chunk781

lemma complete_chunk782 : ∀ i : Fin 200, Compatible (156400 + i.val) →
    (table.lookup (156400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk782 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 156400 156600 :=
  FiniteIntervals.of_fin 156400 200 complete_chunk782

lemma complete_chunk783 : ∀ i : Fin 200, Compatible (156600 + i.val) →
    (table.lookup (156600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk783 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 156600 156800 :=
  FiniteIntervals.of_fin 156600 200 complete_chunk783

lemma complete_chunk784 : ∀ i : Fin 200, Compatible (156800 + i.val) →
    (table.lookup (156800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk784 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 156800 157000 :=
  FiniteIntervals.of_fin 156800 200 complete_chunk784

lemma complete_chunk785 : ∀ i : Fin 200, Compatible (157000 + i.val) →
    (table.lookup (157000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk785 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 157000 157200 :=
  FiniteIntervals.of_fin 157000 200 complete_chunk785

lemma complete_chunk786 : ∀ i : Fin 200, Compatible (157200 + i.val) →
    (table.lookup (157200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk786 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 157200 157400 :=
  FiniteIntervals.of_fin 157200 200 complete_chunk786

lemma complete_chunk787 : ∀ i : Fin 200, Compatible (157400 + i.val) →
    (table.lookup (157400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk787 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 157400 157600 :=
  FiniteIntervals.of_fin 157400 200 complete_chunk787

lemma complete_chunk788 : ∀ i : Fin 200, Compatible (157600 + i.val) →
    (table.lookup (157600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk788 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 157600 157800 :=
  FiniteIntervals.of_fin 157600 200 complete_chunk788

lemma complete_chunk789 : ∀ i : Fin 200, Compatible (157800 + i.val) →
    (table.lookup (157800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk789 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 157800 158000 :=
  FiniteIntervals.of_fin 157800 200 complete_chunk789

#print axioms interval_chunk780
end Erdos184Work.PureFiveFilter4
