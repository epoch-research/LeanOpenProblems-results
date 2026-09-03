import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5460 : ∀ i : Fin 200, Compatible (1092000 + i.val) →
    (table.lookup (1092000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5460 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1092000 1092200 :=
  FiniteIntervals.of_fin 1092000 200 complete_chunk5460

lemma complete_chunk5461 : ∀ i : Fin 200, Compatible (1092200 + i.val) →
    (table.lookup (1092200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5461 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1092200 1092400 :=
  FiniteIntervals.of_fin 1092200 200 complete_chunk5461

lemma complete_chunk5462 : ∀ i : Fin 200, Compatible (1092400 + i.val) →
    (table.lookup (1092400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5462 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1092400 1092600 :=
  FiniteIntervals.of_fin 1092400 200 complete_chunk5462

lemma complete_chunk5463 : ∀ i : Fin 200, Compatible (1092600 + i.val) →
    (table.lookup (1092600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5463 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1092600 1092800 :=
  FiniteIntervals.of_fin 1092600 200 complete_chunk5463

lemma complete_chunk5464 : ∀ i : Fin 200, Compatible (1092800 + i.val) →
    (table.lookup (1092800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5464 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1092800 1093000 :=
  FiniteIntervals.of_fin 1092800 200 complete_chunk5464

lemma complete_chunk5465 : ∀ i : Fin 200, Compatible (1093000 + i.val) →
    (table.lookup (1093000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5465 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1093000 1093200 :=
  FiniteIntervals.of_fin 1093000 200 complete_chunk5465

lemma complete_chunk5466 : ∀ i : Fin 200, Compatible (1093200 + i.val) →
    (table.lookup (1093200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5466 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1093200 1093400 :=
  FiniteIntervals.of_fin 1093200 200 complete_chunk5466

lemma complete_chunk5467 : ∀ i : Fin 200, Compatible (1093400 + i.val) →
    (table.lookup (1093400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5467 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1093400 1093600 :=
  FiniteIntervals.of_fin 1093400 200 complete_chunk5467

lemma complete_chunk5468 : ∀ i : Fin 200, Compatible (1093600 + i.val) →
    (table.lookup (1093600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5468 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1093600 1093800 :=
  FiniteIntervals.of_fin 1093600 200 complete_chunk5468

lemma complete_chunk5469 : ∀ i : Fin 200, Compatible (1093800 + i.val) →
    (table.lookup (1093800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5469 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1093800 1094000 :=
  FiniteIntervals.of_fin 1093800 200 complete_chunk5469

#print axioms interval_chunk5460
end Erdos184Work.PureFiveFilter4
