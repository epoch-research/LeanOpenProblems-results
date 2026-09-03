import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3860 : ∀ i : Fin 200, Compatible (772000 + i.val) →
    (table.lookup (772000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3860 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 772000 772200 :=
  FiniteIntervals.of_fin 772000 200 complete_chunk3860

lemma complete_chunk3861 : ∀ i : Fin 200, Compatible (772200 + i.val) →
    (table.lookup (772200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3861 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 772200 772400 :=
  FiniteIntervals.of_fin 772200 200 complete_chunk3861

lemma complete_chunk3862 : ∀ i : Fin 200, Compatible (772400 + i.val) →
    (table.lookup (772400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3862 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 772400 772600 :=
  FiniteIntervals.of_fin 772400 200 complete_chunk3862

lemma complete_chunk3863 : ∀ i : Fin 200, Compatible (772600 + i.val) →
    (table.lookup (772600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3863 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 772600 772800 :=
  FiniteIntervals.of_fin 772600 200 complete_chunk3863

lemma complete_chunk3864 : ∀ i : Fin 200, Compatible (772800 + i.val) →
    (table.lookup (772800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3864 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 772800 773000 :=
  FiniteIntervals.of_fin 772800 200 complete_chunk3864

lemma complete_chunk3865 : ∀ i : Fin 200, Compatible (773000 + i.val) →
    (table.lookup (773000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3865 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 773000 773200 :=
  FiniteIntervals.of_fin 773000 200 complete_chunk3865

lemma complete_chunk3866 : ∀ i : Fin 200, Compatible (773200 + i.val) →
    (table.lookup (773200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3866 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 773200 773400 :=
  FiniteIntervals.of_fin 773200 200 complete_chunk3866

lemma complete_chunk3867 : ∀ i : Fin 200, Compatible (773400 + i.val) →
    (table.lookup (773400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3867 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 773400 773600 :=
  FiniteIntervals.of_fin 773400 200 complete_chunk3867

lemma complete_chunk3868 : ∀ i : Fin 200, Compatible (773600 + i.val) →
    (table.lookup (773600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3868 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 773600 773800 :=
  FiniteIntervals.of_fin 773600 200 complete_chunk3868

lemma complete_chunk3869 : ∀ i : Fin 200, Compatible (773800 + i.val) →
    (table.lookup (773800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3869 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 773800 774000 :=
  FiniteIntervals.of_fin 773800 200 complete_chunk3869

#print axioms interval_chunk3860
end Erdos184Work.PureFiveFilter4
