import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4870 : ∀ i : Fin 200, Compatible (974000 + i.val) →
    (table.lookup (974000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4870 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 974000 974200 :=
  FiniteIntervals.of_fin 974000 200 complete_chunk4870

lemma complete_chunk4871 : ∀ i : Fin 200, Compatible (974200 + i.val) →
    (table.lookup (974200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4871 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 974200 974400 :=
  FiniteIntervals.of_fin 974200 200 complete_chunk4871

lemma complete_chunk4872 : ∀ i : Fin 200, Compatible (974400 + i.val) →
    (table.lookup (974400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4872 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 974400 974600 :=
  FiniteIntervals.of_fin 974400 200 complete_chunk4872

lemma complete_chunk4873 : ∀ i : Fin 200, Compatible (974600 + i.val) →
    (table.lookup (974600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4873 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 974600 974800 :=
  FiniteIntervals.of_fin 974600 200 complete_chunk4873

lemma complete_chunk4874 : ∀ i : Fin 200, Compatible (974800 + i.val) →
    (table.lookup (974800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4874 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 974800 975000 :=
  FiniteIntervals.of_fin 974800 200 complete_chunk4874

lemma complete_chunk4875 : ∀ i : Fin 200, Compatible (975000 + i.val) →
    (table.lookup (975000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4875 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 975000 975200 :=
  FiniteIntervals.of_fin 975000 200 complete_chunk4875

lemma complete_chunk4876 : ∀ i : Fin 200, Compatible (975200 + i.val) →
    (table.lookup (975200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4876 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 975200 975400 :=
  FiniteIntervals.of_fin 975200 200 complete_chunk4876

lemma complete_chunk4877 : ∀ i : Fin 200, Compatible (975400 + i.val) →
    (table.lookup (975400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4877 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 975400 975600 :=
  FiniteIntervals.of_fin 975400 200 complete_chunk4877

lemma complete_chunk4878 : ∀ i : Fin 200, Compatible (975600 + i.val) →
    (table.lookup (975600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4878 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 975600 975800 :=
  FiniteIntervals.of_fin 975600 200 complete_chunk4878

lemma complete_chunk4879 : ∀ i : Fin 200, Compatible (975800 + i.val) →
    (table.lookup (975800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4879 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 975800 976000 :=
  FiniteIntervals.of_fin 975800 200 complete_chunk4879

#print axioms interval_chunk4870
end Erdos184Work.PureFiveFilter4
