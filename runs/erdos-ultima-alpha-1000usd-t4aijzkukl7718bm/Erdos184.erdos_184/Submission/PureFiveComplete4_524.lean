import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5240 : ∀ i : Fin 200, Compatible (1048000 + i.val) →
    (table.lookup (1048000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5240 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1048000 1048200 :=
  FiniteIntervals.of_fin 1048000 200 complete_chunk5240

lemma complete_chunk5241 : ∀ i : Fin 200, Compatible (1048200 + i.val) →
    (table.lookup (1048200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5241 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1048200 1048400 :=
  FiniteIntervals.of_fin 1048200 200 complete_chunk5241

lemma complete_chunk5242 : ∀ i : Fin 200, Compatible (1048400 + i.val) →
    (table.lookup (1048400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5242 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1048400 1048600 :=
  FiniteIntervals.of_fin 1048400 200 complete_chunk5242

lemma complete_chunk5243 : ∀ i : Fin 200, Compatible (1048600 + i.val) →
    (table.lookup (1048600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5243 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1048600 1048800 :=
  FiniteIntervals.of_fin 1048600 200 complete_chunk5243

lemma complete_chunk5244 : ∀ i : Fin 200, Compatible (1048800 + i.val) →
    (table.lookup (1048800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5244 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1048800 1049000 :=
  FiniteIntervals.of_fin 1048800 200 complete_chunk5244

lemma complete_chunk5245 : ∀ i : Fin 200, Compatible (1049000 + i.val) →
    (table.lookup (1049000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5245 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1049000 1049200 :=
  FiniteIntervals.of_fin 1049000 200 complete_chunk5245

lemma complete_chunk5246 : ∀ i : Fin 200, Compatible (1049200 + i.val) →
    (table.lookup (1049200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5246 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1049200 1049400 :=
  FiniteIntervals.of_fin 1049200 200 complete_chunk5246

lemma complete_chunk5247 : ∀ i : Fin 200, Compatible (1049400 + i.val) →
    (table.lookup (1049400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5247 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1049400 1049600 :=
  FiniteIntervals.of_fin 1049400 200 complete_chunk5247

lemma complete_chunk5248 : ∀ i : Fin 200, Compatible (1049600 + i.val) →
    (table.lookup (1049600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5248 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1049600 1049800 :=
  FiniteIntervals.of_fin 1049600 200 complete_chunk5248

lemma complete_chunk5249 : ∀ i : Fin 200, Compatible (1049800 + i.val) →
    (table.lookup (1049800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5249 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1049800 1050000 :=
  FiniteIntervals.of_fin 1049800 200 complete_chunk5249

#print axioms interval_chunk5240
end Erdos184Work.PureFiveFilter4
