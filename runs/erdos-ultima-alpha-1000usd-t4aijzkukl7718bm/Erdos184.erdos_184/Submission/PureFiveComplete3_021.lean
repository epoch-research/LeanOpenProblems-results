import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk210 : ∀ i : Fin 200, Compatible (42000 + i.val) →
    (table.lookup (42000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 42000 42200 :=
  FiniteIntervals.of_fin 42000 200 complete_chunk210

lemma complete_chunk211 : ∀ i : Fin 200, Compatible (42200 + i.val) →
    (table.lookup (42200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 42200 42400 :=
  FiniteIntervals.of_fin 42200 200 complete_chunk211

lemma complete_chunk212 : ∀ i : Fin 200, Compatible (42400 + i.val) →
    (table.lookup (42400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 42400 42600 :=
  FiniteIntervals.of_fin 42400 200 complete_chunk212

lemma complete_chunk213 : ∀ i : Fin 200, Compatible (42600 + i.val) →
    (table.lookup (42600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 42600 42800 :=
  FiniteIntervals.of_fin 42600 200 complete_chunk213

lemma complete_chunk214 : ∀ i : Fin 200, Compatible (42800 + i.val) →
    (table.lookup (42800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 42800 43000 :=
  FiniteIntervals.of_fin 42800 200 complete_chunk214

lemma complete_chunk215 : ∀ i : Fin 200, Compatible (43000 + i.val) →
    (table.lookup (43000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 43000 43200 :=
  FiniteIntervals.of_fin 43000 200 complete_chunk215

lemma complete_chunk216 : ∀ i : Fin 200, Compatible (43200 + i.val) →
    (table.lookup (43200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 43200 43400 :=
  FiniteIntervals.of_fin 43200 200 complete_chunk216

lemma complete_chunk217 : ∀ i : Fin 200, Compatible (43400 + i.val) →
    (table.lookup (43400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 43400 43600 :=
  FiniteIntervals.of_fin 43400 200 complete_chunk217

lemma complete_chunk218 : ∀ i : Fin 200, Compatible (43600 + i.val) →
    (table.lookup (43600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 43600 43800 :=
  FiniteIntervals.of_fin 43600 200 complete_chunk218

lemma complete_chunk219 : ∀ i : Fin 200, Compatible (43800 + i.val) →
    (table.lookup (43800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 43800 44000 :=
  FiniteIntervals.of_fin 43800 200 complete_chunk219

#print axioms interval_chunk210
end Erdos184Work.PureFiveFilter3
