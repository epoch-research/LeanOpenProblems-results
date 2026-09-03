import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2890 : ∀ i : Fin 200, Compatible (578000 + i.val) →
    (table.lookup (578000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2890 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 578000 578200 :=
  FiniteIntervals.of_fin 578000 200 complete_chunk2890

lemma complete_chunk2891 : ∀ i : Fin 200, Compatible (578200 + i.val) →
    (table.lookup (578200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2891 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 578200 578400 :=
  FiniteIntervals.of_fin 578200 200 complete_chunk2891

lemma complete_chunk2892 : ∀ i : Fin 200, Compatible (578400 + i.val) →
    (table.lookup (578400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2892 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 578400 578600 :=
  FiniteIntervals.of_fin 578400 200 complete_chunk2892

lemma complete_chunk2893 : ∀ i : Fin 200, Compatible (578600 + i.val) →
    (table.lookup (578600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2893 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 578600 578800 :=
  FiniteIntervals.of_fin 578600 200 complete_chunk2893

lemma complete_chunk2894 : ∀ i : Fin 200, Compatible (578800 + i.val) →
    (table.lookup (578800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2894 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 578800 579000 :=
  FiniteIntervals.of_fin 578800 200 complete_chunk2894

lemma complete_chunk2895 : ∀ i : Fin 200, Compatible (579000 + i.val) →
    (table.lookup (579000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2895 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 579000 579200 :=
  FiniteIntervals.of_fin 579000 200 complete_chunk2895

lemma complete_chunk2896 : ∀ i : Fin 200, Compatible (579200 + i.val) →
    (table.lookup (579200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2896 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 579200 579400 :=
  FiniteIntervals.of_fin 579200 200 complete_chunk2896

lemma complete_chunk2897 : ∀ i : Fin 200, Compatible (579400 + i.val) →
    (table.lookup (579400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2897 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 579400 579600 :=
  FiniteIntervals.of_fin 579400 200 complete_chunk2897

lemma complete_chunk2898 : ∀ i : Fin 200, Compatible (579600 + i.val) →
    (table.lookup (579600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2898 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 579600 579800 :=
  FiniteIntervals.of_fin 579600 200 complete_chunk2898

lemma complete_chunk2899 : ∀ i : Fin 200, Compatible (579800 + i.val) →
    (table.lookup (579800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2899 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 579800 580000 :=
  FiniteIntervals.of_fin 579800 200 complete_chunk2899

#print axioms interval_chunk2890
end Erdos184Work.PureFiveFilter4
