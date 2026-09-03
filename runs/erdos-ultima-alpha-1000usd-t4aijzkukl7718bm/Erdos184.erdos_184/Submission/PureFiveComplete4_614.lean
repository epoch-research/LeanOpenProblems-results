import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6140 : ∀ i : Fin 200, Compatible (1228000 + i.val) →
    (table.lookup (1228000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1228000 1228200 :=
  FiniteIntervals.of_fin 1228000 200 complete_chunk6140

lemma complete_chunk6141 : ∀ i : Fin 200, Compatible (1228200 + i.val) →
    (table.lookup (1228200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1228200 1228400 :=
  FiniteIntervals.of_fin 1228200 200 complete_chunk6141

lemma complete_chunk6142 : ∀ i : Fin 200, Compatible (1228400 + i.val) →
    (table.lookup (1228400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1228400 1228600 :=
  FiniteIntervals.of_fin 1228400 200 complete_chunk6142

lemma complete_chunk6143 : ∀ i : Fin 200, Compatible (1228600 + i.val) →
    (table.lookup (1228600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1228600 1228800 :=
  FiniteIntervals.of_fin 1228600 200 complete_chunk6143

lemma complete_chunk6144 : ∀ i : Fin 200, Compatible (1228800 + i.val) →
    (table.lookup (1228800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1228800 1229000 :=
  FiniteIntervals.of_fin 1228800 200 complete_chunk6144

lemma complete_chunk6145 : ∀ i : Fin 200, Compatible (1229000 + i.val) →
    (table.lookup (1229000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1229000 1229200 :=
  FiniteIntervals.of_fin 1229000 200 complete_chunk6145

lemma complete_chunk6146 : ∀ i : Fin 200, Compatible (1229200 + i.val) →
    (table.lookup (1229200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1229200 1229400 :=
  FiniteIntervals.of_fin 1229200 200 complete_chunk6146

lemma complete_chunk6147 : ∀ i : Fin 200, Compatible (1229400 + i.val) →
    (table.lookup (1229400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1229400 1229600 :=
  FiniteIntervals.of_fin 1229400 200 complete_chunk6147

lemma complete_chunk6148 : ∀ i : Fin 200, Compatible (1229600 + i.val) →
    (table.lookup (1229600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1229600 1229800 :=
  FiniteIntervals.of_fin 1229600 200 complete_chunk6148

lemma complete_chunk6149 : ∀ i : Fin 200, Compatible (1229800 + i.val) →
    (table.lookup (1229800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1229800 1230000 :=
  FiniteIntervals.of_fin 1229800 200 complete_chunk6149

#print axioms interval_chunk6140
end Erdos184Work.PureFiveFilter4
