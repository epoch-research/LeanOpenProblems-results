import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3280 : ∀ i : Fin 200, Compatible (656000 + i.val) →
    (table.lookup (656000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3280 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 656000 656200 :=
  FiniteIntervals.of_fin 656000 200 complete_chunk3280

lemma complete_chunk3281 : ∀ i : Fin 200, Compatible (656200 + i.val) →
    (table.lookup (656200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3281 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 656200 656400 :=
  FiniteIntervals.of_fin 656200 200 complete_chunk3281

lemma complete_chunk3282 : ∀ i : Fin 200, Compatible (656400 + i.val) →
    (table.lookup (656400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3282 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 656400 656600 :=
  FiniteIntervals.of_fin 656400 200 complete_chunk3282

lemma complete_chunk3283 : ∀ i : Fin 200, Compatible (656600 + i.val) →
    (table.lookup (656600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3283 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 656600 656800 :=
  FiniteIntervals.of_fin 656600 200 complete_chunk3283

lemma complete_chunk3284 : ∀ i : Fin 200, Compatible (656800 + i.val) →
    (table.lookup (656800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3284 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 656800 657000 :=
  FiniteIntervals.of_fin 656800 200 complete_chunk3284

lemma complete_chunk3285 : ∀ i : Fin 200, Compatible (657000 + i.val) →
    (table.lookup (657000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3285 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 657000 657200 :=
  FiniteIntervals.of_fin 657000 200 complete_chunk3285

lemma complete_chunk3286 : ∀ i : Fin 200, Compatible (657200 + i.val) →
    (table.lookup (657200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3286 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 657200 657400 :=
  FiniteIntervals.of_fin 657200 200 complete_chunk3286

lemma complete_chunk3287 : ∀ i : Fin 200, Compatible (657400 + i.val) →
    (table.lookup (657400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3287 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 657400 657600 :=
  FiniteIntervals.of_fin 657400 200 complete_chunk3287

lemma complete_chunk3288 : ∀ i : Fin 200, Compatible (657600 + i.val) →
    (table.lookup (657600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3288 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 657600 657800 :=
  FiniteIntervals.of_fin 657600 200 complete_chunk3288

lemma complete_chunk3289 : ∀ i : Fin 200, Compatible (657800 + i.val) →
    (table.lookup (657800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3289 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 657800 658000 :=
  FiniteIntervals.of_fin 657800 200 complete_chunk3289

#print axioms interval_chunk3280
end Erdos184Work.PureFiveFilter4
