import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4910 : ∀ i : Fin 200, Compatible (982000 + i.val) →
    (table.lookup (982000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4910 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 982000 982200 :=
  FiniteIntervals.of_fin 982000 200 complete_chunk4910

lemma complete_chunk4911 : ∀ i : Fin 200, Compatible (982200 + i.val) →
    (table.lookup (982200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4911 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 982200 982400 :=
  FiniteIntervals.of_fin 982200 200 complete_chunk4911

lemma complete_chunk4912 : ∀ i : Fin 200, Compatible (982400 + i.val) →
    (table.lookup (982400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4912 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 982400 982600 :=
  FiniteIntervals.of_fin 982400 200 complete_chunk4912

lemma complete_chunk4913 : ∀ i : Fin 200, Compatible (982600 + i.val) →
    (table.lookup (982600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4913 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 982600 982800 :=
  FiniteIntervals.of_fin 982600 200 complete_chunk4913

lemma complete_chunk4914 : ∀ i : Fin 200, Compatible (982800 + i.val) →
    (table.lookup (982800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4914 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 982800 983000 :=
  FiniteIntervals.of_fin 982800 200 complete_chunk4914

lemma complete_chunk4915 : ∀ i : Fin 200, Compatible (983000 + i.val) →
    (table.lookup (983000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4915 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 983000 983200 :=
  FiniteIntervals.of_fin 983000 200 complete_chunk4915

lemma complete_chunk4916 : ∀ i : Fin 200, Compatible (983200 + i.val) →
    (table.lookup (983200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4916 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 983200 983400 :=
  FiniteIntervals.of_fin 983200 200 complete_chunk4916

lemma complete_chunk4917 : ∀ i : Fin 200, Compatible (983400 + i.val) →
    (table.lookup (983400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4917 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 983400 983600 :=
  FiniteIntervals.of_fin 983400 200 complete_chunk4917

lemma complete_chunk4918 : ∀ i : Fin 200, Compatible (983600 + i.val) →
    (table.lookup (983600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4918 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 983600 983800 :=
  FiniteIntervals.of_fin 983600 200 complete_chunk4918

lemma complete_chunk4919 : ∀ i : Fin 200, Compatible (983800 + i.val) →
    (table.lookup (983800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4919 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 983800 984000 :=
  FiniteIntervals.of_fin 983800 200 complete_chunk4919

#print axioms interval_chunk4910
end Erdos184Work.PureFiveFilter4
