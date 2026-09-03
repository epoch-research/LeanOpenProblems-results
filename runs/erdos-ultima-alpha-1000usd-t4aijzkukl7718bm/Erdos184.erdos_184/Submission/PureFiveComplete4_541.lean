import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5410 : ∀ i : Fin 200, Compatible (1082000 + i.val) →
    (table.lookup (1082000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5410 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1082000 1082200 :=
  FiniteIntervals.of_fin 1082000 200 complete_chunk5410

lemma complete_chunk5411 : ∀ i : Fin 200, Compatible (1082200 + i.val) →
    (table.lookup (1082200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5411 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1082200 1082400 :=
  FiniteIntervals.of_fin 1082200 200 complete_chunk5411

lemma complete_chunk5412 : ∀ i : Fin 200, Compatible (1082400 + i.val) →
    (table.lookup (1082400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5412 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1082400 1082600 :=
  FiniteIntervals.of_fin 1082400 200 complete_chunk5412

lemma complete_chunk5413 : ∀ i : Fin 200, Compatible (1082600 + i.val) →
    (table.lookup (1082600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5413 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1082600 1082800 :=
  FiniteIntervals.of_fin 1082600 200 complete_chunk5413

lemma complete_chunk5414 : ∀ i : Fin 200, Compatible (1082800 + i.val) →
    (table.lookup (1082800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5414 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1082800 1083000 :=
  FiniteIntervals.of_fin 1082800 200 complete_chunk5414

lemma complete_chunk5415 : ∀ i : Fin 200, Compatible (1083000 + i.val) →
    (table.lookup (1083000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5415 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1083000 1083200 :=
  FiniteIntervals.of_fin 1083000 200 complete_chunk5415

lemma complete_chunk5416 : ∀ i : Fin 200, Compatible (1083200 + i.val) →
    (table.lookup (1083200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5416 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1083200 1083400 :=
  FiniteIntervals.of_fin 1083200 200 complete_chunk5416

lemma complete_chunk5417 : ∀ i : Fin 200, Compatible (1083400 + i.val) →
    (table.lookup (1083400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5417 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1083400 1083600 :=
  FiniteIntervals.of_fin 1083400 200 complete_chunk5417

lemma complete_chunk5418 : ∀ i : Fin 200, Compatible (1083600 + i.val) →
    (table.lookup (1083600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5418 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1083600 1083800 :=
  FiniteIntervals.of_fin 1083600 200 complete_chunk5418

lemma complete_chunk5419 : ∀ i : Fin 200, Compatible (1083800 + i.val) →
    (table.lookup (1083800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5419 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1083800 1084000 :=
  FiniteIntervals.of_fin 1083800 200 complete_chunk5419

#print axioms interval_chunk5410
end Erdos184Work.PureFiveFilter4
