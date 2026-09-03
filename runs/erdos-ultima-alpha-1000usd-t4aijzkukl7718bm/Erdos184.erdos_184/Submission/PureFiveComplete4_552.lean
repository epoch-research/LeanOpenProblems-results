import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5520 : ∀ i : Fin 200, Compatible (1104000 + i.val) →
    (table.lookup (1104000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5520 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1104000 1104200 :=
  FiniteIntervals.of_fin 1104000 200 complete_chunk5520

lemma complete_chunk5521 : ∀ i : Fin 200, Compatible (1104200 + i.val) →
    (table.lookup (1104200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5521 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1104200 1104400 :=
  FiniteIntervals.of_fin 1104200 200 complete_chunk5521

lemma complete_chunk5522 : ∀ i : Fin 200, Compatible (1104400 + i.val) →
    (table.lookup (1104400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5522 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1104400 1104600 :=
  FiniteIntervals.of_fin 1104400 200 complete_chunk5522

lemma complete_chunk5523 : ∀ i : Fin 200, Compatible (1104600 + i.val) →
    (table.lookup (1104600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5523 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1104600 1104800 :=
  FiniteIntervals.of_fin 1104600 200 complete_chunk5523

lemma complete_chunk5524 : ∀ i : Fin 200, Compatible (1104800 + i.val) →
    (table.lookup (1104800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5524 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1104800 1105000 :=
  FiniteIntervals.of_fin 1104800 200 complete_chunk5524

lemma complete_chunk5525 : ∀ i : Fin 200, Compatible (1105000 + i.val) →
    (table.lookup (1105000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5525 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1105000 1105200 :=
  FiniteIntervals.of_fin 1105000 200 complete_chunk5525

lemma complete_chunk5526 : ∀ i : Fin 200, Compatible (1105200 + i.val) →
    (table.lookup (1105200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5526 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1105200 1105400 :=
  FiniteIntervals.of_fin 1105200 200 complete_chunk5526

lemma complete_chunk5527 : ∀ i : Fin 200, Compatible (1105400 + i.val) →
    (table.lookup (1105400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5527 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1105400 1105600 :=
  FiniteIntervals.of_fin 1105400 200 complete_chunk5527

lemma complete_chunk5528 : ∀ i : Fin 200, Compatible (1105600 + i.val) →
    (table.lookup (1105600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5528 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1105600 1105800 :=
  FiniteIntervals.of_fin 1105600 200 complete_chunk5528

lemma complete_chunk5529 : ∀ i : Fin 200, Compatible (1105800 + i.val) →
    (table.lookup (1105800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5529 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1105800 1106000 :=
  FiniteIntervals.of_fin 1105800 200 complete_chunk5529

#print axioms interval_chunk5520
end Erdos184Work.PureFiveFilter4
