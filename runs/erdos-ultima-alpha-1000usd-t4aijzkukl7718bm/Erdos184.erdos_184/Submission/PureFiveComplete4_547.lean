import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5470 : ∀ i : Fin 200, Compatible (1094000 + i.val) →
    (table.lookup (1094000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5470 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1094000 1094200 :=
  FiniteIntervals.of_fin 1094000 200 complete_chunk5470

lemma complete_chunk5471 : ∀ i : Fin 200, Compatible (1094200 + i.val) →
    (table.lookup (1094200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5471 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1094200 1094400 :=
  FiniteIntervals.of_fin 1094200 200 complete_chunk5471

lemma complete_chunk5472 : ∀ i : Fin 200, Compatible (1094400 + i.val) →
    (table.lookup (1094400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5472 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1094400 1094600 :=
  FiniteIntervals.of_fin 1094400 200 complete_chunk5472

lemma complete_chunk5473 : ∀ i : Fin 200, Compatible (1094600 + i.val) →
    (table.lookup (1094600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5473 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1094600 1094800 :=
  FiniteIntervals.of_fin 1094600 200 complete_chunk5473

lemma complete_chunk5474 : ∀ i : Fin 200, Compatible (1094800 + i.val) →
    (table.lookup (1094800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5474 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1094800 1095000 :=
  FiniteIntervals.of_fin 1094800 200 complete_chunk5474

lemma complete_chunk5475 : ∀ i : Fin 200, Compatible (1095000 + i.val) →
    (table.lookup (1095000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5475 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1095000 1095200 :=
  FiniteIntervals.of_fin 1095000 200 complete_chunk5475

lemma complete_chunk5476 : ∀ i : Fin 200, Compatible (1095200 + i.val) →
    (table.lookup (1095200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5476 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1095200 1095400 :=
  FiniteIntervals.of_fin 1095200 200 complete_chunk5476

lemma complete_chunk5477 : ∀ i : Fin 200, Compatible (1095400 + i.val) →
    (table.lookup (1095400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5477 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1095400 1095600 :=
  FiniteIntervals.of_fin 1095400 200 complete_chunk5477

lemma complete_chunk5478 : ∀ i : Fin 200, Compatible (1095600 + i.val) →
    (table.lookup (1095600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5478 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1095600 1095800 :=
  FiniteIntervals.of_fin 1095600 200 complete_chunk5478

lemma complete_chunk5479 : ∀ i : Fin 200, Compatible (1095800 + i.val) →
    (table.lookup (1095800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5479 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1095800 1096000 :=
  FiniteIntervals.of_fin 1095800 200 complete_chunk5479

#print axioms interval_chunk5470
end Erdos184Work.PureFiveFilter4
