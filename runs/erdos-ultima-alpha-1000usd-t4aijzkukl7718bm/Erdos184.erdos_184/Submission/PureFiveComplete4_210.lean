import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2100 : ∀ i : Fin 200, Compatible (420000 + i.val) →
    (table.lookup (420000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2100 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 420000 420200 :=
  FiniteIntervals.of_fin 420000 200 complete_chunk2100

lemma complete_chunk2101 : ∀ i : Fin 200, Compatible (420200 + i.val) →
    (table.lookup (420200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2101 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 420200 420400 :=
  FiniteIntervals.of_fin 420200 200 complete_chunk2101

lemma complete_chunk2102 : ∀ i : Fin 200, Compatible (420400 + i.val) →
    (table.lookup (420400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2102 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 420400 420600 :=
  FiniteIntervals.of_fin 420400 200 complete_chunk2102

lemma complete_chunk2103 : ∀ i : Fin 200, Compatible (420600 + i.val) →
    (table.lookup (420600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2103 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 420600 420800 :=
  FiniteIntervals.of_fin 420600 200 complete_chunk2103

lemma complete_chunk2104 : ∀ i : Fin 200, Compatible (420800 + i.val) →
    (table.lookup (420800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2104 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 420800 421000 :=
  FiniteIntervals.of_fin 420800 200 complete_chunk2104

lemma complete_chunk2105 : ∀ i : Fin 200, Compatible (421000 + i.val) →
    (table.lookup (421000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2105 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 421000 421200 :=
  FiniteIntervals.of_fin 421000 200 complete_chunk2105

lemma complete_chunk2106 : ∀ i : Fin 200, Compatible (421200 + i.val) →
    (table.lookup (421200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2106 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 421200 421400 :=
  FiniteIntervals.of_fin 421200 200 complete_chunk2106

lemma complete_chunk2107 : ∀ i : Fin 200, Compatible (421400 + i.val) →
    (table.lookup (421400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2107 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 421400 421600 :=
  FiniteIntervals.of_fin 421400 200 complete_chunk2107

lemma complete_chunk2108 : ∀ i : Fin 200, Compatible (421600 + i.val) →
    (table.lookup (421600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2108 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 421600 421800 :=
  FiniteIntervals.of_fin 421600 200 complete_chunk2108

lemma complete_chunk2109 : ∀ i : Fin 200, Compatible (421800 + i.val) →
    (table.lookup (421800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2109 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 421800 422000 :=
  FiniteIntervals.of_fin 421800 200 complete_chunk2109

#print axioms interval_chunk2100
end Erdos184Work.PureFiveFilter4
