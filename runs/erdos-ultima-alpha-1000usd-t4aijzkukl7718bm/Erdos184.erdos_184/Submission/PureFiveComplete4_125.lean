import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1250 : ∀ i : Fin 200, Compatible (250000 + i.val) →
    (table.lookup (250000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1250 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 250000 250200 :=
  FiniteIntervals.of_fin 250000 200 complete_chunk1250

lemma complete_chunk1251 : ∀ i : Fin 200, Compatible (250200 + i.val) →
    (table.lookup (250200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1251 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 250200 250400 :=
  FiniteIntervals.of_fin 250200 200 complete_chunk1251

lemma complete_chunk1252 : ∀ i : Fin 200, Compatible (250400 + i.val) →
    (table.lookup (250400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1252 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 250400 250600 :=
  FiniteIntervals.of_fin 250400 200 complete_chunk1252

lemma complete_chunk1253 : ∀ i : Fin 200, Compatible (250600 + i.val) →
    (table.lookup (250600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1253 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 250600 250800 :=
  FiniteIntervals.of_fin 250600 200 complete_chunk1253

lemma complete_chunk1254 : ∀ i : Fin 200, Compatible (250800 + i.val) →
    (table.lookup (250800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1254 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 250800 251000 :=
  FiniteIntervals.of_fin 250800 200 complete_chunk1254

lemma complete_chunk1255 : ∀ i : Fin 200, Compatible (251000 + i.val) →
    (table.lookup (251000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1255 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 251000 251200 :=
  FiniteIntervals.of_fin 251000 200 complete_chunk1255

lemma complete_chunk1256 : ∀ i : Fin 200, Compatible (251200 + i.val) →
    (table.lookup (251200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1256 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 251200 251400 :=
  FiniteIntervals.of_fin 251200 200 complete_chunk1256

lemma complete_chunk1257 : ∀ i : Fin 200, Compatible (251400 + i.val) →
    (table.lookup (251400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1257 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 251400 251600 :=
  FiniteIntervals.of_fin 251400 200 complete_chunk1257

lemma complete_chunk1258 : ∀ i : Fin 200, Compatible (251600 + i.val) →
    (table.lookup (251600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1258 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 251600 251800 :=
  FiniteIntervals.of_fin 251600 200 complete_chunk1258

lemma complete_chunk1259 : ∀ i : Fin 200, Compatible (251800 + i.val) →
    (table.lookup (251800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1259 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 251800 252000 :=
  FiniteIntervals.of_fin 251800 200 complete_chunk1259

#print axioms interval_chunk1250
end Erdos184Work.PureFiveFilter4
