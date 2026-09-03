import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5260 : ∀ i : Fin 200, Compatible (1052000 + i.val) →
    (table.lookup (1052000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5260 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1052000 1052200 :=
  FiniteIntervals.of_fin 1052000 200 complete_chunk5260

lemma complete_chunk5261 : ∀ i : Fin 200, Compatible (1052200 + i.val) →
    (table.lookup (1052200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5261 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1052200 1052400 :=
  FiniteIntervals.of_fin 1052200 200 complete_chunk5261

lemma complete_chunk5262 : ∀ i : Fin 200, Compatible (1052400 + i.val) →
    (table.lookup (1052400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5262 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1052400 1052600 :=
  FiniteIntervals.of_fin 1052400 200 complete_chunk5262

lemma complete_chunk5263 : ∀ i : Fin 200, Compatible (1052600 + i.val) →
    (table.lookup (1052600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5263 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1052600 1052800 :=
  FiniteIntervals.of_fin 1052600 200 complete_chunk5263

lemma complete_chunk5264 : ∀ i : Fin 200, Compatible (1052800 + i.val) →
    (table.lookup (1052800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5264 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1052800 1053000 :=
  FiniteIntervals.of_fin 1052800 200 complete_chunk5264

lemma complete_chunk5265 : ∀ i : Fin 200, Compatible (1053000 + i.val) →
    (table.lookup (1053000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5265 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1053000 1053200 :=
  FiniteIntervals.of_fin 1053000 200 complete_chunk5265

lemma complete_chunk5266 : ∀ i : Fin 200, Compatible (1053200 + i.val) →
    (table.lookup (1053200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5266 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1053200 1053400 :=
  FiniteIntervals.of_fin 1053200 200 complete_chunk5266

lemma complete_chunk5267 : ∀ i : Fin 200, Compatible (1053400 + i.val) →
    (table.lookup (1053400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5267 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1053400 1053600 :=
  FiniteIntervals.of_fin 1053400 200 complete_chunk5267

lemma complete_chunk5268 : ∀ i : Fin 200, Compatible (1053600 + i.val) →
    (table.lookup (1053600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5268 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1053600 1053800 :=
  FiniteIntervals.of_fin 1053600 200 complete_chunk5268

lemma complete_chunk5269 : ∀ i : Fin 200, Compatible (1053800 + i.val) →
    (table.lookup (1053800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5269 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1053800 1054000 :=
  FiniteIntervals.of_fin 1053800 200 complete_chunk5269

#print axioms interval_chunk5260
end Erdos184Work.PureFiveFilter4
