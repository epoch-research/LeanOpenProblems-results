import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk270 : ∀ i : Fin 200, Compatible (54000 + i.val) →
    (table.lookup (54000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk270 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54000 54200 :=
  FiniteIntervals.of_fin 54000 200 complete_chunk270

lemma complete_chunk271 : ∀ i : Fin 200, Compatible (54200 + i.val) →
    (table.lookup (54200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk271 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54200 54400 :=
  FiniteIntervals.of_fin 54200 200 complete_chunk271

lemma complete_chunk272 : ∀ i : Fin 200, Compatible (54400 + i.val) →
    (table.lookup (54400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk272 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54400 54600 :=
  FiniteIntervals.of_fin 54400 200 complete_chunk272

lemma complete_chunk273 : ∀ i : Fin 200, Compatible (54600 + i.val) →
    (table.lookup (54600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk273 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54600 54800 :=
  FiniteIntervals.of_fin 54600 200 complete_chunk273

lemma complete_chunk274 : ∀ i : Fin 200, Compatible (54800 + i.val) →
    (table.lookup (54800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk274 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 54800 55000 :=
  FiniteIntervals.of_fin 54800 200 complete_chunk274

lemma complete_chunk275 : ∀ i : Fin 200, Compatible (55000 + i.val) →
    (table.lookup (55000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk275 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55000 55200 :=
  FiniteIntervals.of_fin 55000 200 complete_chunk275

lemma complete_chunk276 : ∀ i : Fin 200, Compatible (55200 + i.val) →
    (table.lookup (55200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk276 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55200 55400 :=
  FiniteIntervals.of_fin 55200 200 complete_chunk276

lemma complete_chunk277 : ∀ i : Fin 200, Compatible (55400 + i.val) →
    (table.lookup (55400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk277 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55400 55600 :=
  FiniteIntervals.of_fin 55400 200 complete_chunk277

lemma complete_chunk278 : ∀ i : Fin 200, Compatible (55600 + i.val) →
    (table.lookup (55600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk278 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55600 55800 :=
  FiniteIntervals.of_fin 55600 200 complete_chunk278

lemma complete_chunk279 : ∀ i : Fin 200, Compatible (55800 + i.val) →
    (table.lookup (55800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk279 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 55800 56000 :=
  FiniteIntervals.of_fin 55800 200 complete_chunk279

#print axioms interval_chunk270
end Erdos184Work.PureFiveFilter3
