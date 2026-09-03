import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5590 : ∀ i : Fin 200, Compatible (1118000 + i.val) →
    (table.lookup (1118000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5590 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1118000 1118200 :=
  FiniteIntervals.of_fin 1118000 200 complete_chunk5590

lemma complete_chunk5591 : ∀ i : Fin 200, Compatible (1118200 + i.val) →
    (table.lookup (1118200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5591 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1118200 1118400 :=
  FiniteIntervals.of_fin 1118200 200 complete_chunk5591

lemma complete_chunk5592 : ∀ i : Fin 200, Compatible (1118400 + i.val) →
    (table.lookup (1118400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5592 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1118400 1118600 :=
  FiniteIntervals.of_fin 1118400 200 complete_chunk5592

lemma complete_chunk5593 : ∀ i : Fin 200, Compatible (1118600 + i.val) →
    (table.lookup (1118600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5593 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1118600 1118800 :=
  FiniteIntervals.of_fin 1118600 200 complete_chunk5593

lemma complete_chunk5594 : ∀ i : Fin 200, Compatible (1118800 + i.val) →
    (table.lookup (1118800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5594 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1118800 1119000 :=
  FiniteIntervals.of_fin 1118800 200 complete_chunk5594

lemma complete_chunk5595 : ∀ i : Fin 200, Compatible (1119000 + i.val) →
    (table.lookup (1119000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5595 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1119000 1119200 :=
  FiniteIntervals.of_fin 1119000 200 complete_chunk5595

lemma complete_chunk5596 : ∀ i : Fin 200, Compatible (1119200 + i.val) →
    (table.lookup (1119200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5596 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1119200 1119400 :=
  FiniteIntervals.of_fin 1119200 200 complete_chunk5596

lemma complete_chunk5597 : ∀ i : Fin 200, Compatible (1119400 + i.val) →
    (table.lookup (1119400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5597 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1119400 1119600 :=
  FiniteIntervals.of_fin 1119400 200 complete_chunk5597

lemma complete_chunk5598 : ∀ i : Fin 200, Compatible (1119600 + i.val) →
    (table.lookup (1119600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5598 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1119600 1119800 :=
  FiniteIntervals.of_fin 1119600 200 complete_chunk5598

lemma complete_chunk5599 : ∀ i : Fin 200, Compatible (1119800 + i.val) →
    (table.lookup (1119800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5599 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1119800 1120000 :=
  FiniteIntervals.of_fin 1119800 200 complete_chunk5599

#print axioms interval_chunk5590
end Erdos184Work.PureFiveFilter4
