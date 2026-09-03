import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4030 : ∀ i : Fin 200, Compatible (806000 + i.val) →
    (table.lookup (806000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4030 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 806000 806200 :=
  FiniteIntervals.of_fin 806000 200 complete_chunk4030

lemma complete_chunk4031 : ∀ i : Fin 200, Compatible (806200 + i.val) →
    (table.lookup (806200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4031 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 806200 806400 :=
  FiniteIntervals.of_fin 806200 200 complete_chunk4031

lemma complete_chunk4032 : ∀ i : Fin 200, Compatible (806400 + i.val) →
    (table.lookup (806400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4032 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 806400 806600 :=
  FiniteIntervals.of_fin 806400 200 complete_chunk4032

lemma complete_chunk4033 : ∀ i : Fin 200, Compatible (806600 + i.val) →
    (table.lookup (806600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4033 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 806600 806800 :=
  FiniteIntervals.of_fin 806600 200 complete_chunk4033

lemma complete_chunk4034 : ∀ i : Fin 200, Compatible (806800 + i.val) →
    (table.lookup (806800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4034 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 806800 807000 :=
  FiniteIntervals.of_fin 806800 200 complete_chunk4034

lemma complete_chunk4035 : ∀ i : Fin 200, Compatible (807000 + i.val) →
    (table.lookup (807000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4035 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 807000 807200 :=
  FiniteIntervals.of_fin 807000 200 complete_chunk4035

lemma complete_chunk4036 : ∀ i : Fin 200, Compatible (807200 + i.val) →
    (table.lookup (807200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4036 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 807200 807400 :=
  FiniteIntervals.of_fin 807200 200 complete_chunk4036

lemma complete_chunk4037 : ∀ i : Fin 200, Compatible (807400 + i.val) →
    (table.lookup (807400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4037 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 807400 807600 :=
  FiniteIntervals.of_fin 807400 200 complete_chunk4037

lemma complete_chunk4038 : ∀ i : Fin 200, Compatible (807600 + i.val) →
    (table.lookup (807600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4038 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 807600 807800 :=
  FiniteIntervals.of_fin 807600 200 complete_chunk4038

lemma complete_chunk4039 : ∀ i : Fin 200, Compatible (807800 + i.val) →
    (table.lookup (807800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4039 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 807800 808000 :=
  FiniteIntervals.of_fin 807800 200 complete_chunk4039

#print axioms interval_chunk4030
end Erdos184Work.PureFiveFilter4
