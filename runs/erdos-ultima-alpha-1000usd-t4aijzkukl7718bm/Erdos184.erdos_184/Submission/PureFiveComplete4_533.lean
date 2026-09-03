import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5330 : ∀ i : Fin 200, Compatible (1066000 + i.val) →
    (table.lookup (1066000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5330 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1066000 1066200 :=
  FiniteIntervals.of_fin 1066000 200 complete_chunk5330

lemma complete_chunk5331 : ∀ i : Fin 200, Compatible (1066200 + i.val) →
    (table.lookup (1066200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5331 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1066200 1066400 :=
  FiniteIntervals.of_fin 1066200 200 complete_chunk5331

lemma complete_chunk5332 : ∀ i : Fin 200, Compatible (1066400 + i.val) →
    (table.lookup (1066400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5332 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1066400 1066600 :=
  FiniteIntervals.of_fin 1066400 200 complete_chunk5332

lemma complete_chunk5333 : ∀ i : Fin 200, Compatible (1066600 + i.val) →
    (table.lookup (1066600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5333 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1066600 1066800 :=
  FiniteIntervals.of_fin 1066600 200 complete_chunk5333

lemma complete_chunk5334 : ∀ i : Fin 200, Compatible (1066800 + i.val) →
    (table.lookup (1066800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5334 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1066800 1067000 :=
  FiniteIntervals.of_fin 1066800 200 complete_chunk5334

lemma complete_chunk5335 : ∀ i : Fin 200, Compatible (1067000 + i.val) →
    (table.lookup (1067000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5335 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1067000 1067200 :=
  FiniteIntervals.of_fin 1067000 200 complete_chunk5335

lemma complete_chunk5336 : ∀ i : Fin 200, Compatible (1067200 + i.val) →
    (table.lookup (1067200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5336 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1067200 1067400 :=
  FiniteIntervals.of_fin 1067200 200 complete_chunk5336

lemma complete_chunk5337 : ∀ i : Fin 200, Compatible (1067400 + i.val) →
    (table.lookup (1067400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5337 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1067400 1067600 :=
  FiniteIntervals.of_fin 1067400 200 complete_chunk5337

lemma complete_chunk5338 : ∀ i : Fin 200, Compatible (1067600 + i.val) →
    (table.lookup (1067600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5338 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1067600 1067800 :=
  FiniteIntervals.of_fin 1067600 200 complete_chunk5338

lemma complete_chunk5339 : ∀ i : Fin 200, Compatible (1067800 + i.val) →
    (table.lookup (1067800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5339 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1067800 1068000 :=
  FiniteIntervals.of_fin 1067800 200 complete_chunk5339

#print axioms interval_chunk5330
end Erdos184Work.PureFiveFilter4
