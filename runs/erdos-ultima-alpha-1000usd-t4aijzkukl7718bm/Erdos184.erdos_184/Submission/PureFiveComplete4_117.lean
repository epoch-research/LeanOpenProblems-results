import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1170 : ∀ i : Fin 200, Compatible (234000 + i.val) →
    (table.lookup (234000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 234000 234200 :=
  FiniteIntervals.of_fin 234000 200 complete_chunk1170

lemma complete_chunk1171 : ∀ i : Fin 200, Compatible (234200 + i.val) →
    (table.lookup (234200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 234200 234400 :=
  FiniteIntervals.of_fin 234200 200 complete_chunk1171

lemma complete_chunk1172 : ∀ i : Fin 200, Compatible (234400 + i.val) →
    (table.lookup (234400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 234400 234600 :=
  FiniteIntervals.of_fin 234400 200 complete_chunk1172

lemma complete_chunk1173 : ∀ i : Fin 200, Compatible (234600 + i.val) →
    (table.lookup (234600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 234600 234800 :=
  FiniteIntervals.of_fin 234600 200 complete_chunk1173

lemma complete_chunk1174 : ∀ i : Fin 200, Compatible (234800 + i.val) →
    (table.lookup (234800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 234800 235000 :=
  FiniteIntervals.of_fin 234800 200 complete_chunk1174

lemma complete_chunk1175 : ∀ i : Fin 200, Compatible (235000 + i.val) →
    (table.lookup (235000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 235000 235200 :=
  FiniteIntervals.of_fin 235000 200 complete_chunk1175

lemma complete_chunk1176 : ∀ i : Fin 200, Compatible (235200 + i.val) →
    (table.lookup (235200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 235200 235400 :=
  FiniteIntervals.of_fin 235200 200 complete_chunk1176

lemma complete_chunk1177 : ∀ i : Fin 200, Compatible (235400 + i.val) →
    (table.lookup (235400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 235400 235600 :=
  FiniteIntervals.of_fin 235400 200 complete_chunk1177

lemma complete_chunk1178 : ∀ i : Fin 200, Compatible (235600 + i.val) →
    (table.lookup (235600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 235600 235800 :=
  FiniteIntervals.of_fin 235600 200 complete_chunk1178

lemma complete_chunk1179 : ∀ i : Fin 200, Compatible (235800 + i.val) →
    (table.lookup (235800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 235800 236000 :=
  FiniteIntervals.of_fin 235800 200 complete_chunk1179

#print axioms interval_chunk1170
end Erdos184Work.PureFiveFilter4
