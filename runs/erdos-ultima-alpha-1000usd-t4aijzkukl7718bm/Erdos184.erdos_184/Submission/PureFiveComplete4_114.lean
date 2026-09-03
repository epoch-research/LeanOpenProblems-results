import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1140 : ∀ i : Fin 200, Compatible (228000 + i.val) →
    (table.lookup (228000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 228000 228200 :=
  FiniteIntervals.of_fin 228000 200 complete_chunk1140

lemma complete_chunk1141 : ∀ i : Fin 200, Compatible (228200 + i.val) →
    (table.lookup (228200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 228200 228400 :=
  FiniteIntervals.of_fin 228200 200 complete_chunk1141

lemma complete_chunk1142 : ∀ i : Fin 200, Compatible (228400 + i.val) →
    (table.lookup (228400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 228400 228600 :=
  FiniteIntervals.of_fin 228400 200 complete_chunk1142

lemma complete_chunk1143 : ∀ i : Fin 200, Compatible (228600 + i.val) →
    (table.lookup (228600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 228600 228800 :=
  FiniteIntervals.of_fin 228600 200 complete_chunk1143

lemma complete_chunk1144 : ∀ i : Fin 200, Compatible (228800 + i.val) →
    (table.lookup (228800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 228800 229000 :=
  FiniteIntervals.of_fin 228800 200 complete_chunk1144

lemma complete_chunk1145 : ∀ i : Fin 200, Compatible (229000 + i.val) →
    (table.lookup (229000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 229000 229200 :=
  FiniteIntervals.of_fin 229000 200 complete_chunk1145

lemma complete_chunk1146 : ∀ i : Fin 200, Compatible (229200 + i.val) →
    (table.lookup (229200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 229200 229400 :=
  FiniteIntervals.of_fin 229200 200 complete_chunk1146

lemma complete_chunk1147 : ∀ i : Fin 200, Compatible (229400 + i.val) →
    (table.lookup (229400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 229400 229600 :=
  FiniteIntervals.of_fin 229400 200 complete_chunk1147

lemma complete_chunk1148 : ∀ i : Fin 200, Compatible (229600 + i.val) →
    (table.lookup (229600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 229600 229800 :=
  FiniteIntervals.of_fin 229600 200 complete_chunk1148

lemma complete_chunk1149 : ∀ i : Fin 200, Compatible (229800 + i.val) →
    (table.lookup (229800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 229800 230000 :=
  FiniteIntervals.of_fin 229800 200 complete_chunk1149

#print axioms interval_chunk1140
end Erdos184Work.PureFiveFilter4
