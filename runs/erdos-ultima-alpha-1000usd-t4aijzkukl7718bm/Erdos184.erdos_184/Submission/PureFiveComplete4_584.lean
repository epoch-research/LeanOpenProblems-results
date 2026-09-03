import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5840 : ∀ i : Fin 200, Compatible (1168000 + i.val) →
    (table.lookup (1168000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5840 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1168000 1168200 :=
  FiniteIntervals.of_fin 1168000 200 complete_chunk5840

lemma complete_chunk5841 : ∀ i : Fin 200, Compatible (1168200 + i.val) →
    (table.lookup (1168200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5841 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1168200 1168400 :=
  FiniteIntervals.of_fin 1168200 200 complete_chunk5841

lemma complete_chunk5842 : ∀ i : Fin 200, Compatible (1168400 + i.val) →
    (table.lookup (1168400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5842 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1168400 1168600 :=
  FiniteIntervals.of_fin 1168400 200 complete_chunk5842

lemma complete_chunk5843 : ∀ i : Fin 200, Compatible (1168600 + i.val) →
    (table.lookup (1168600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5843 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1168600 1168800 :=
  FiniteIntervals.of_fin 1168600 200 complete_chunk5843

lemma complete_chunk5844 : ∀ i : Fin 200, Compatible (1168800 + i.val) →
    (table.lookup (1168800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5844 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1168800 1169000 :=
  FiniteIntervals.of_fin 1168800 200 complete_chunk5844

lemma complete_chunk5845 : ∀ i : Fin 200, Compatible (1169000 + i.val) →
    (table.lookup (1169000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5845 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1169000 1169200 :=
  FiniteIntervals.of_fin 1169000 200 complete_chunk5845

lemma complete_chunk5846 : ∀ i : Fin 200, Compatible (1169200 + i.val) →
    (table.lookup (1169200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5846 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1169200 1169400 :=
  FiniteIntervals.of_fin 1169200 200 complete_chunk5846

lemma complete_chunk5847 : ∀ i : Fin 200, Compatible (1169400 + i.val) →
    (table.lookup (1169400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5847 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1169400 1169600 :=
  FiniteIntervals.of_fin 1169400 200 complete_chunk5847

lemma complete_chunk5848 : ∀ i : Fin 200, Compatible (1169600 + i.val) →
    (table.lookup (1169600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5848 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1169600 1169800 :=
  FiniteIntervals.of_fin 1169600 200 complete_chunk5848

lemma complete_chunk5849 : ∀ i : Fin 200, Compatible (1169800 + i.val) →
    (table.lookup (1169800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5849 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1169800 1170000 :=
  FiniteIntervals.of_fin 1169800 200 complete_chunk5849

#print axioms interval_chunk5840
end Erdos184Work.PureFiveFilter4
