import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1220 : ∀ i : Fin 200, Compatible (244000 + i.val) →
    (table.lookup (244000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1220 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 244000 244200 :=
  FiniteIntervals.of_fin 244000 200 complete_chunk1220

lemma complete_chunk1221 : ∀ i : Fin 200, Compatible (244200 + i.val) →
    (table.lookup (244200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1221 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 244200 244400 :=
  FiniteIntervals.of_fin 244200 200 complete_chunk1221

lemma complete_chunk1222 : ∀ i : Fin 200, Compatible (244400 + i.val) →
    (table.lookup (244400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1222 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 244400 244600 :=
  FiniteIntervals.of_fin 244400 200 complete_chunk1222

lemma complete_chunk1223 : ∀ i : Fin 200, Compatible (244600 + i.val) →
    (table.lookup (244600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1223 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 244600 244800 :=
  FiniteIntervals.of_fin 244600 200 complete_chunk1223

lemma complete_chunk1224 : ∀ i : Fin 200, Compatible (244800 + i.val) →
    (table.lookup (244800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1224 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 244800 245000 :=
  FiniteIntervals.of_fin 244800 200 complete_chunk1224

lemma complete_chunk1225 : ∀ i : Fin 200, Compatible (245000 + i.val) →
    (table.lookup (245000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1225 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 245000 245200 :=
  FiniteIntervals.of_fin 245000 200 complete_chunk1225

lemma complete_chunk1226 : ∀ i : Fin 200, Compatible (245200 + i.val) →
    (table.lookup (245200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1226 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 245200 245400 :=
  FiniteIntervals.of_fin 245200 200 complete_chunk1226

lemma complete_chunk1227 : ∀ i : Fin 200, Compatible (245400 + i.val) →
    (table.lookup (245400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1227 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 245400 245600 :=
  FiniteIntervals.of_fin 245400 200 complete_chunk1227

lemma complete_chunk1228 : ∀ i : Fin 200, Compatible (245600 + i.val) →
    (table.lookup (245600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1228 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 245600 245800 :=
  FiniteIntervals.of_fin 245600 200 complete_chunk1228

lemma complete_chunk1229 : ∀ i : Fin 200, Compatible (245800 + i.val) →
    (table.lookup (245800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1229 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 245800 246000 :=
  FiniteIntervals.of_fin 245800 200 complete_chunk1229

#print axioms interval_chunk1220
end Erdos184Work.PureFiveFilter4
