import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk120 : ∀ i : Fin 200, Compatible (24000 + i.val) →
    (table.lookup (24000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 24000 24200 :=
  FiniteIntervals.of_fin 24000 200 complete_chunk120

lemma complete_chunk121 : ∀ i : Fin 200, Compatible (24200 + i.val) →
    (table.lookup (24200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 24200 24400 :=
  FiniteIntervals.of_fin 24200 200 complete_chunk121

lemma complete_chunk122 : ∀ i : Fin 200, Compatible (24400 + i.val) →
    (table.lookup (24400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 24400 24600 :=
  FiniteIntervals.of_fin 24400 200 complete_chunk122

lemma complete_chunk123 : ∀ i : Fin 200, Compatible (24600 + i.val) →
    (table.lookup (24600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 24600 24800 :=
  FiniteIntervals.of_fin 24600 200 complete_chunk123

lemma complete_chunk124 : ∀ i : Fin 200, Compatible (24800 + i.val) →
    (table.lookup (24800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 24800 25000 :=
  FiniteIntervals.of_fin 24800 200 complete_chunk124

lemma complete_chunk125 : ∀ i : Fin 200, Compatible (25000 + i.val) →
    (table.lookup (25000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 25000 25200 :=
  FiniteIntervals.of_fin 25000 200 complete_chunk125

lemma complete_chunk126 : ∀ i : Fin 200, Compatible (25200 + i.val) →
    (table.lookup (25200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 25200 25400 :=
  FiniteIntervals.of_fin 25200 200 complete_chunk126

lemma complete_chunk127 : ∀ i : Fin 200, Compatible (25400 + i.val) →
    (table.lookup (25400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 25400 25600 :=
  FiniteIntervals.of_fin 25400 200 complete_chunk127

lemma complete_chunk128 : ∀ i : Fin 200, Compatible (25600 + i.val) →
    (table.lookup (25600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 25600 25800 :=
  FiniteIntervals.of_fin 25600 200 complete_chunk128

lemma complete_chunk129 : ∀ i : Fin 200, Compatible (25800 + i.val) →
    (table.lookup (25800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 25800 26000 :=
  FiniteIntervals.of_fin 25800 200 complete_chunk129

#print axioms interval_chunk120
end Erdos184Work.PureFiveFilter3
