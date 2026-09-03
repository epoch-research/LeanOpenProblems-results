import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1180 : ∀ i : Fin 200, Compatible (236000 + i.val) →
    (table.lookup (236000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1180 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 236000 236200 :=
  FiniteIntervals.of_fin 236000 200 complete_chunk1180

lemma complete_chunk1181 : ∀ i : Fin 200, Compatible (236200 + i.val) →
    (table.lookup (236200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1181 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 236200 236400 :=
  FiniteIntervals.of_fin 236200 200 complete_chunk1181

lemma complete_chunk1182 : ∀ i : Fin 200, Compatible (236400 + i.val) →
    (table.lookup (236400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1182 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 236400 236600 :=
  FiniteIntervals.of_fin 236400 200 complete_chunk1182

lemma complete_chunk1183 : ∀ i : Fin 200, Compatible (236600 + i.val) →
    (table.lookup (236600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1183 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 236600 236800 :=
  FiniteIntervals.of_fin 236600 200 complete_chunk1183

lemma complete_chunk1184 : ∀ i : Fin 200, Compatible (236800 + i.val) →
    (table.lookup (236800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1184 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 236800 237000 :=
  FiniteIntervals.of_fin 236800 200 complete_chunk1184

lemma complete_chunk1185 : ∀ i : Fin 200, Compatible (237000 + i.val) →
    (table.lookup (237000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1185 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 237000 237200 :=
  FiniteIntervals.of_fin 237000 200 complete_chunk1185

lemma complete_chunk1186 : ∀ i : Fin 200, Compatible (237200 + i.val) →
    (table.lookup (237200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1186 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 237200 237400 :=
  FiniteIntervals.of_fin 237200 200 complete_chunk1186

lemma complete_chunk1187 : ∀ i : Fin 200, Compatible (237400 + i.val) →
    (table.lookup (237400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1187 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 237400 237600 :=
  FiniteIntervals.of_fin 237400 200 complete_chunk1187

lemma complete_chunk1188 : ∀ i : Fin 200, Compatible (237600 + i.val) →
    (table.lookup (237600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1188 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 237600 237800 :=
  FiniteIntervals.of_fin 237600 200 complete_chunk1188

lemma complete_chunk1189 : ∀ i : Fin 200, Compatible (237800 + i.val) →
    (table.lookup (237800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1189 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 237800 238000 :=
  FiniteIntervals.of_fin 237800 200 complete_chunk1189

#print axioms interval_chunk1180
end Erdos184Work.PureFiveFilter4
