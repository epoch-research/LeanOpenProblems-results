import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk840 : ∀ i : Fin 200, Compatible (168000 + i.val) →
    (table.lookup (168000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk840 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 168000 168200 :=
  FiniteIntervals.of_fin 168000 200 complete_chunk840

lemma complete_chunk841 : ∀ i : Fin 200, Compatible (168200 + i.val) →
    (table.lookup (168200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk841 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 168200 168400 :=
  FiniteIntervals.of_fin 168200 200 complete_chunk841

lemma complete_chunk842 : ∀ i : Fin 200, Compatible (168400 + i.val) →
    (table.lookup (168400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk842 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 168400 168600 :=
  FiniteIntervals.of_fin 168400 200 complete_chunk842

lemma complete_chunk843 : ∀ i : Fin 200, Compatible (168600 + i.val) →
    (table.lookup (168600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk843 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 168600 168800 :=
  FiniteIntervals.of_fin 168600 200 complete_chunk843

lemma complete_chunk844 : ∀ i : Fin 200, Compatible (168800 + i.val) →
    (table.lookup (168800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk844 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 168800 169000 :=
  FiniteIntervals.of_fin 168800 200 complete_chunk844

lemma complete_chunk845 : ∀ i : Fin 200, Compatible (169000 + i.val) →
    (table.lookup (169000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk845 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 169000 169200 :=
  FiniteIntervals.of_fin 169000 200 complete_chunk845

lemma complete_chunk846 : ∀ i : Fin 200, Compatible (169200 + i.val) →
    (table.lookup (169200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk846 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 169200 169400 :=
  FiniteIntervals.of_fin 169200 200 complete_chunk846

lemma complete_chunk847 : ∀ i : Fin 200, Compatible (169400 + i.val) →
    (table.lookup (169400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk847 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 169400 169600 :=
  FiniteIntervals.of_fin 169400 200 complete_chunk847

lemma complete_chunk848 : ∀ i : Fin 200, Compatible (169600 + i.val) →
    (table.lookup (169600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk848 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 169600 169800 :=
  FiniteIntervals.of_fin 169600 200 complete_chunk848

lemma complete_chunk849 : ∀ i : Fin 200, Compatible (169800 + i.val) →
    (table.lookup (169800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk849 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 169800 170000 :=
  FiniteIntervals.of_fin 169800 200 complete_chunk849

#print axioms interval_chunk840
end Erdos184Work.PureFiveFilter4
