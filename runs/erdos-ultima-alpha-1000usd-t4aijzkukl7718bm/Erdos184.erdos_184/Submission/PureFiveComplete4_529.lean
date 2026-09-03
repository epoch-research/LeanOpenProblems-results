import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5290 : ∀ i : Fin 200, Compatible (1058000 + i.val) →
    (table.lookup (1058000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5290 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1058000 1058200 :=
  FiniteIntervals.of_fin 1058000 200 complete_chunk5290

lemma complete_chunk5291 : ∀ i : Fin 200, Compatible (1058200 + i.val) →
    (table.lookup (1058200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5291 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1058200 1058400 :=
  FiniteIntervals.of_fin 1058200 200 complete_chunk5291

lemma complete_chunk5292 : ∀ i : Fin 200, Compatible (1058400 + i.val) →
    (table.lookup (1058400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5292 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1058400 1058600 :=
  FiniteIntervals.of_fin 1058400 200 complete_chunk5292

lemma complete_chunk5293 : ∀ i : Fin 200, Compatible (1058600 + i.val) →
    (table.lookup (1058600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5293 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1058600 1058800 :=
  FiniteIntervals.of_fin 1058600 200 complete_chunk5293

lemma complete_chunk5294 : ∀ i : Fin 200, Compatible (1058800 + i.val) →
    (table.lookup (1058800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5294 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1058800 1059000 :=
  FiniteIntervals.of_fin 1058800 200 complete_chunk5294

lemma complete_chunk5295 : ∀ i : Fin 200, Compatible (1059000 + i.val) →
    (table.lookup (1059000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5295 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1059000 1059200 :=
  FiniteIntervals.of_fin 1059000 200 complete_chunk5295

lemma complete_chunk5296 : ∀ i : Fin 200, Compatible (1059200 + i.val) →
    (table.lookup (1059200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5296 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1059200 1059400 :=
  FiniteIntervals.of_fin 1059200 200 complete_chunk5296

lemma complete_chunk5297 : ∀ i : Fin 200, Compatible (1059400 + i.val) →
    (table.lookup (1059400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5297 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1059400 1059600 :=
  FiniteIntervals.of_fin 1059400 200 complete_chunk5297

lemma complete_chunk5298 : ∀ i : Fin 200, Compatible (1059600 + i.val) →
    (table.lookup (1059600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5298 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1059600 1059800 :=
  FiniteIntervals.of_fin 1059600 200 complete_chunk5298

lemma complete_chunk5299 : ∀ i : Fin 200, Compatible (1059800 + i.val) →
    (table.lookup (1059800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5299 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1059800 1060000 :=
  FiniteIntervals.of_fin 1059800 200 complete_chunk5299

#print axioms interval_chunk5290
end Erdos184Work.PureFiveFilter4
