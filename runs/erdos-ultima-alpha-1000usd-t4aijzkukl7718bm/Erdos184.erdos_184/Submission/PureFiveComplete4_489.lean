import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4890 : ∀ i : Fin 200, Compatible (978000 + i.val) →
    (table.lookup (978000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4890 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 978000 978200 :=
  FiniteIntervals.of_fin 978000 200 complete_chunk4890

lemma complete_chunk4891 : ∀ i : Fin 200, Compatible (978200 + i.val) →
    (table.lookup (978200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4891 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 978200 978400 :=
  FiniteIntervals.of_fin 978200 200 complete_chunk4891

lemma complete_chunk4892 : ∀ i : Fin 200, Compatible (978400 + i.val) →
    (table.lookup (978400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4892 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 978400 978600 :=
  FiniteIntervals.of_fin 978400 200 complete_chunk4892

lemma complete_chunk4893 : ∀ i : Fin 200, Compatible (978600 + i.val) →
    (table.lookup (978600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4893 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 978600 978800 :=
  FiniteIntervals.of_fin 978600 200 complete_chunk4893

lemma complete_chunk4894 : ∀ i : Fin 200, Compatible (978800 + i.val) →
    (table.lookup (978800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4894 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 978800 979000 :=
  FiniteIntervals.of_fin 978800 200 complete_chunk4894

lemma complete_chunk4895 : ∀ i : Fin 200, Compatible (979000 + i.val) →
    (table.lookup (979000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4895 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 979000 979200 :=
  FiniteIntervals.of_fin 979000 200 complete_chunk4895

lemma complete_chunk4896 : ∀ i : Fin 200, Compatible (979200 + i.val) →
    (table.lookup (979200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4896 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 979200 979400 :=
  FiniteIntervals.of_fin 979200 200 complete_chunk4896

lemma complete_chunk4897 : ∀ i : Fin 200, Compatible (979400 + i.val) →
    (table.lookup (979400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4897 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 979400 979600 :=
  FiniteIntervals.of_fin 979400 200 complete_chunk4897

lemma complete_chunk4898 : ∀ i : Fin 200, Compatible (979600 + i.val) →
    (table.lookup (979600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4898 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 979600 979800 :=
  FiniteIntervals.of_fin 979600 200 complete_chunk4898

lemma complete_chunk4899 : ∀ i : Fin 200, Compatible (979800 + i.val) →
    (table.lookup (979800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4899 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 979800 980000 :=
  FiniteIntervals.of_fin 979800 200 complete_chunk4899

#print axioms interval_chunk4890
end Erdos184Work.PureFiveFilter4
