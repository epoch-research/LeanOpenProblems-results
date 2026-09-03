import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk170 : ∀ i : Fin 200, Compatible (34000 + i.val) →
    (table.lookup (34000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 34000 34200 :=
  FiniteIntervals.of_fin 34000 200 complete_chunk170

lemma complete_chunk171 : ∀ i : Fin 200, Compatible (34200 + i.val) →
    (table.lookup (34200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 34200 34400 :=
  FiniteIntervals.of_fin 34200 200 complete_chunk171

lemma complete_chunk172 : ∀ i : Fin 200, Compatible (34400 + i.val) →
    (table.lookup (34400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 34400 34600 :=
  FiniteIntervals.of_fin 34400 200 complete_chunk172

lemma complete_chunk173 : ∀ i : Fin 200, Compatible (34600 + i.val) →
    (table.lookup (34600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 34600 34800 :=
  FiniteIntervals.of_fin 34600 200 complete_chunk173

lemma complete_chunk174 : ∀ i : Fin 200, Compatible (34800 + i.val) →
    (table.lookup (34800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 34800 35000 :=
  FiniteIntervals.of_fin 34800 200 complete_chunk174

lemma complete_chunk175 : ∀ i : Fin 200, Compatible (35000 + i.val) →
    (table.lookup (35000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 35000 35200 :=
  FiniteIntervals.of_fin 35000 200 complete_chunk175

lemma complete_chunk176 : ∀ i : Fin 200, Compatible (35200 + i.val) →
    (table.lookup (35200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 35200 35400 :=
  FiniteIntervals.of_fin 35200 200 complete_chunk176

lemma complete_chunk177 : ∀ i : Fin 200, Compatible (35400 + i.val) →
    (table.lookup (35400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 35400 35600 :=
  FiniteIntervals.of_fin 35400 200 complete_chunk177

lemma complete_chunk178 : ∀ i : Fin 200, Compatible (35600 + i.val) →
    (table.lookup (35600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 35600 35800 :=
  FiniteIntervals.of_fin 35600 200 complete_chunk178

lemma complete_chunk179 : ∀ i : Fin 200, Compatible (35800 + i.val) →
    (table.lookup (35800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 35800 36000 :=
  FiniteIntervals.of_fin 35800 200 complete_chunk179

#print axioms interval_chunk170
end Erdos184Work.PureFiveFilter3
