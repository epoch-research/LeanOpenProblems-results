import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2860 : ∀ i : Fin 200, Compatible (572000 + i.val) →
    (table.lookup (572000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2860 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 572000 572200 :=
  FiniteIntervals.of_fin 572000 200 complete_chunk2860

lemma complete_chunk2861 : ∀ i : Fin 200, Compatible (572200 + i.val) →
    (table.lookup (572200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2861 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 572200 572400 :=
  FiniteIntervals.of_fin 572200 200 complete_chunk2861

lemma complete_chunk2862 : ∀ i : Fin 200, Compatible (572400 + i.val) →
    (table.lookup (572400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2862 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 572400 572600 :=
  FiniteIntervals.of_fin 572400 200 complete_chunk2862

lemma complete_chunk2863 : ∀ i : Fin 200, Compatible (572600 + i.val) →
    (table.lookup (572600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2863 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 572600 572800 :=
  FiniteIntervals.of_fin 572600 200 complete_chunk2863

lemma complete_chunk2864 : ∀ i : Fin 200, Compatible (572800 + i.val) →
    (table.lookup (572800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2864 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 572800 573000 :=
  FiniteIntervals.of_fin 572800 200 complete_chunk2864

lemma complete_chunk2865 : ∀ i : Fin 200, Compatible (573000 + i.val) →
    (table.lookup (573000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2865 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 573000 573200 :=
  FiniteIntervals.of_fin 573000 200 complete_chunk2865

lemma complete_chunk2866 : ∀ i : Fin 200, Compatible (573200 + i.val) →
    (table.lookup (573200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2866 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 573200 573400 :=
  FiniteIntervals.of_fin 573200 200 complete_chunk2866

lemma complete_chunk2867 : ∀ i : Fin 200, Compatible (573400 + i.val) →
    (table.lookup (573400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2867 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 573400 573600 :=
  FiniteIntervals.of_fin 573400 200 complete_chunk2867

lemma complete_chunk2868 : ∀ i : Fin 200, Compatible (573600 + i.val) →
    (table.lookup (573600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2868 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 573600 573800 :=
  FiniteIntervals.of_fin 573600 200 complete_chunk2868

lemma complete_chunk2869 : ∀ i : Fin 200, Compatible (573800 + i.val) →
    (table.lookup (573800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2869 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 573800 574000 :=
  FiniteIntervals.of_fin 573800 200 complete_chunk2869

#print axioms interval_chunk2860
end Erdos184Work.PureFiveFilter4
