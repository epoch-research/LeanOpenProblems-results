import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2120 : ∀ i : Fin 200, Compatible (424000 + i.val) →
    (table.lookup (424000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 424000 424200 :=
  FiniteIntervals.of_fin 424000 200 complete_chunk2120

lemma complete_chunk2121 : ∀ i : Fin 200, Compatible (424200 + i.val) →
    (table.lookup (424200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 424200 424400 :=
  FiniteIntervals.of_fin 424200 200 complete_chunk2121

lemma complete_chunk2122 : ∀ i : Fin 200, Compatible (424400 + i.val) →
    (table.lookup (424400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 424400 424600 :=
  FiniteIntervals.of_fin 424400 200 complete_chunk2122

lemma complete_chunk2123 : ∀ i : Fin 200, Compatible (424600 + i.val) →
    (table.lookup (424600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 424600 424800 :=
  FiniteIntervals.of_fin 424600 200 complete_chunk2123

lemma complete_chunk2124 : ∀ i : Fin 200, Compatible (424800 + i.val) →
    (table.lookup (424800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 424800 425000 :=
  FiniteIntervals.of_fin 424800 200 complete_chunk2124

lemma complete_chunk2125 : ∀ i : Fin 200, Compatible (425000 + i.val) →
    (table.lookup (425000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 425000 425200 :=
  FiniteIntervals.of_fin 425000 200 complete_chunk2125

lemma complete_chunk2126 : ∀ i : Fin 200, Compatible (425200 + i.val) →
    (table.lookup (425200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 425200 425400 :=
  FiniteIntervals.of_fin 425200 200 complete_chunk2126

lemma complete_chunk2127 : ∀ i : Fin 200, Compatible (425400 + i.val) →
    (table.lookup (425400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 425400 425600 :=
  FiniteIntervals.of_fin 425400 200 complete_chunk2127

lemma complete_chunk2128 : ∀ i : Fin 200, Compatible (425600 + i.val) →
    (table.lookup (425600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 425600 425800 :=
  FiniteIntervals.of_fin 425600 200 complete_chunk2128

lemma complete_chunk2129 : ∀ i : Fin 200, Compatible (425800 + i.val) →
    (table.lookup (425800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 425800 426000 :=
  FiniteIntervals.of_fin 425800 200 complete_chunk2129

#print axioms interval_chunk2120
end Erdos184Work.PureFiveFilter4
