import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5780 : ∀ i : Fin 200, Compatible (1156000 + i.val) →
    (table.lookup (1156000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5780 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1156000 1156200 :=
  FiniteIntervals.of_fin 1156000 200 complete_chunk5780

lemma complete_chunk5781 : ∀ i : Fin 200, Compatible (1156200 + i.val) →
    (table.lookup (1156200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5781 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1156200 1156400 :=
  FiniteIntervals.of_fin 1156200 200 complete_chunk5781

lemma complete_chunk5782 : ∀ i : Fin 200, Compatible (1156400 + i.val) →
    (table.lookup (1156400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5782 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1156400 1156600 :=
  FiniteIntervals.of_fin 1156400 200 complete_chunk5782

lemma complete_chunk5783 : ∀ i : Fin 200, Compatible (1156600 + i.val) →
    (table.lookup (1156600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5783 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1156600 1156800 :=
  FiniteIntervals.of_fin 1156600 200 complete_chunk5783

lemma complete_chunk5784 : ∀ i : Fin 200, Compatible (1156800 + i.val) →
    (table.lookup (1156800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5784 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1156800 1157000 :=
  FiniteIntervals.of_fin 1156800 200 complete_chunk5784

lemma complete_chunk5785 : ∀ i : Fin 200, Compatible (1157000 + i.val) →
    (table.lookup (1157000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5785 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1157000 1157200 :=
  FiniteIntervals.of_fin 1157000 200 complete_chunk5785

lemma complete_chunk5786 : ∀ i : Fin 200, Compatible (1157200 + i.val) →
    (table.lookup (1157200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5786 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1157200 1157400 :=
  FiniteIntervals.of_fin 1157200 200 complete_chunk5786

lemma complete_chunk5787 : ∀ i : Fin 200, Compatible (1157400 + i.val) →
    (table.lookup (1157400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5787 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1157400 1157600 :=
  FiniteIntervals.of_fin 1157400 200 complete_chunk5787

lemma complete_chunk5788 : ∀ i : Fin 200, Compatible (1157600 + i.val) →
    (table.lookup (1157600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5788 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1157600 1157800 :=
  FiniteIntervals.of_fin 1157600 200 complete_chunk5788

lemma complete_chunk5789 : ∀ i : Fin 200, Compatible (1157800 + i.val) →
    (table.lookup (1157800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5789 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1157800 1158000 :=
  FiniteIntervals.of_fin 1157800 200 complete_chunk5789

#print axioms interval_chunk5780
end Erdos184Work.PureFiveFilter4
