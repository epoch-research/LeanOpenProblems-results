import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4290 : ∀ i : Fin 200, Compatible (858000 + i.val) →
    (table.lookup (858000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4290 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 858000 858200 :=
  FiniteIntervals.of_fin 858000 200 complete_chunk4290

lemma complete_chunk4291 : ∀ i : Fin 200, Compatible (858200 + i.val) →
    (table.lookup (858200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4291 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 858200 858400 :=
  FiniteIntervals.of_fin 858200 200 complete_chunk4291

lemma complete_chunk4292 : ∀ i : Fin 200, Compatible (858400 + i.val) →
    (table.lookup (858400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4292 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 858400 858600 :=
  FiniteIntervals.of_fin 858400 200 complete_chunk4292

lemma complete_chunk4293 : ∀ i : Fin 200, Compatible (858600 + i.val) →
    (table.lookup (858600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4293 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 858600 858800 :=
  FiniteIntervals.of_fin 858600 200 complete_chunk4293

lemma complete_chunk4294 : ∀ i : Fin 200, Compatible (858800 + i.val) →
    (table.lookup (858800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4294 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 858800 859000 :=
  FiniteIntervals.of_fin 858800 200 complete_chunk4294

lemma complete_chunk4295 : ∀ i : Fin 200, Compatible (859000 + i.val) →
    (table.lookup (859000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4295 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 859000 859200 :=
  FiniteIntervals.of_fin 859000 200 complete_chunk4295

lemma complete_chunk4296 : ∀ i : Fin 200, Compatible (859200 + i.val) →
    (table.lookup (859200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4296 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 859200 859400 :=
  FiniteIntervals.of_fin 859200 200 complete_chunk4296

lemma complete_chunk4297 : ∀ i : Fin 200, Compatible (859400 + i.val) →
    (table.lookup (859400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4297 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 859400 859600 :=
  FiniteIntervals.of_fin 859400 200 complete_chunk4297

lemma complete_chunk4298 : ∀ i : Fin 200, Compatible (859600 + i.val) →
    (table.lookup (859600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4298 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 859600 859800 :=
  FiniteIntervals.of_fin 859600 200 complete_chunk4298

lemma complete_chunk4299 : ∀ i : Fin 200, Compatible (859800 + i.val) →
    (table.lookup (859800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4299 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 859800 860000 :=
  FiniteIntervals.of_fin 859800 200 complete_chunk4299

#print axioms interval_chunk4290
end Erdos184Work.PureFiveFilter4
