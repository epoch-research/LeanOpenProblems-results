import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4070 : ∀ i : Fin 200, Compatible (814000 + i.val) →
    (table.lookup (814000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4070 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 814000 814200 :=
  FiniteIntervals.of_fin 814000 200 complete_chunk4070

lemma complete_chunk4071 : ∀ i : Fin 200, Compatible (814200 + i.val) →
    (table.lookup (814200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4071 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 814200 814400 :=
  FiniteIntervals.of_fin 814200 200 complete_chunk4071

lemma complete_chunk4072 : ∀ i : Fin 200, Compatible (814400 + i.val) →
    (table.lookup (814400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4072 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 814400 814600 :=
  FiniteIntervals.of_fin 814400 200 complete_chunk4072

lemma complete_chunk4073 : ∀ i : Fin 200, Compatible (814600 + i.val) →
    (table.lookup (814600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4073 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 814600 814800 :=
  FiniteIntervals.of_fin 814600 200 complete_chunk4073

lemma complete_chunk4074 : ∀ i : Fin 200, Compatible (814800 + i.val) →
    (table.lookup (814800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4074 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 814800 815000 :=
  FiniteIntervals.of_fin 814800 200 complete_chunk4074

lemma complete_chunk4075 : ∀ i : Fin 200, Compatible (815000 + i.val) →
    (table.lookup (815000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4075 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 815000 815200 :=
  FiniteIntervals.of_fin 815000 200 complete_chunk4075

lemma complete_chunk4076 : ∀ i : Fin 200, Compatible (815200 + i.val) →
    (table.lookup (815200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4076 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 815200 815400 :=
  FiniteIntervals.of_fin 815200 200 complete_chunk4076

lemma complete_chunk4077 : ∀ i : Fin 200, Compatible (815400 + i.val) →
    (table.lookup (815400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4077 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 815400 815600 :=
  FiniteIntervals.of_fin 815400 200 complete_chunk4077

lemma complete_chunk4078 : ∀ i : Fin 200, Compatible (815600 + i.val) →
    (table.lookup (815600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4078 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 815600 815800 :=
  FiniteIntervals.of_fin 815600 200 complete_chunk4078

lemma complete_chunk4079 : ∀ i : Fin 200, Compatible (815800 + i.val) →
    (table.lookup (815800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4079 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 815800 816000 :=
  FiniteIntervals.of_fin 815800 200 complete_chunk4079

#print axioms interval_chunk4070
end Erdos184Work.PureFiveFilter4
