import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5320 : ∀ i : Fin 200, Compatible (1064000 + i.val) →
    (table.lookup (1064000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5320 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1064000 1064200 :=
  FiniteIntervals.of_fin 1064000 200 complete_chunk5320

lemma complete_chunk5321 : ∀ i : Fin 200, Compatible (1064200 + i.val) →
    (table.lookup (1064200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5321 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1064200 1064400 :=
  FiniteIntervals.of_fin 1064200 200 complete_chunk5321

lemma complete_chunk5322 : ∀ i : Fin 200, Compatible (1064400 + i.val) →
    (table.lookup (1064400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5322 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1064400 1064600 :=
  FiniteIntervals.of_fin 1064400 200 complete_chunk5322

lemma complete_chunk5323 : ∀ i : Fin 200, Compatible (1064600 + i.val) →
    (table.lookup (1064600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5323 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1064600 1064800 :=
  FiniteIntervals.of_fin 1064600 200 complete_chunk5323

lemma complete_chunk5324 : ∀ i : Fin 200, Compatible (1064800 + i.val) →
    (table.lookup (1064800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5324 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1064800 1065000 :=
  FiniteIntervals.of_fin 1064800 200 complete_chunk5324

lemma complete_chunk5325 : ∀ i : Fin 200, Compatible (1065000 + i.val) →
    (table.lookup (1065000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5325 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1065000 1065200 :=
  FiniteIntervals.of_fin 1065000 200 complete_chunk5325

lemma complete_chunk5326 : ∀ i : Fin 200, Compatible (1065200 + i.val) →
    (table.lookup (1065200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5326 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1065200 1065400 :=
  FiniteIntervals.of_fin 1065200 200 complete_chunk5326

lemma complete_chunk5327 : ∀ i : Fin 200, Compatible (1065400 + i.val) →
    (table.lookup (1065400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5327 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1065400 1065600 :=
  FiniteIntervals.of_fin 1065400 200 complete_chunk5327

lemma complete_chunk5328 : ∀ i : Fin 200, Compatible (1065600 + i.val) →
    (table.lookup (1065600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5328 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1065600 1065800 :=
  FiniteIntervals.of_fin 1065600 200 complete_chunk5328

lemma complete_chunk5329 : ∀ i : Fin 200, Compatible (1065800 + i.val) →
    (table.lookup (1065800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5329 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1065800 1066000 :=
  FiniteIntervals.of_fin 1065800 200 complete_chunk5329

#print axioms interval_chunk5320
end Erdos184Work.PureFiveFilter4
