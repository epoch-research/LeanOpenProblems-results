import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk130 : ∀ i : Fin 200, Compatible (26000 + i.val) →
    (table.lookup (26000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk130 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 26000 26200 :=
  FiniteIntervals.of_fin 26000 200 complete_chunk130

lemma complete_chunk131 : ∀ i : Fin 200, Compatible (26200 + i.val) →
    (table.lookup (26200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk131 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 26200 26400 :=
  FiniteIntervals.of_fin 26200 200 complete_chunk131

lemma complete_chunk132 : ∀ i : Fin 200, Compatible (26400 + i.val) →
    (table.lookup (26400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk132 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 26400 26600 :=
  FiniteIntervals.of_fin 26400 200 complete_chunk132

lemma complete_chunk133 : ∀ i : Fin 200, Compatible (26600 + i.val) →
    (table.lookup (26600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk133 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 26600 26800 :=
  FiniteIntervals.of_fin 26600 200 complete_chunk133

lemma complete_chunk134 : ∀ i : Fin 200, Compatible (26800 + i.val) →
    (table.lookup (26800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk134 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 26800 27000 :=
  FiniteIntervals.of_fin 26800 200 complete_chunk134

lemma complete_chunk135 : ∀ i : Fin 200, Compatible (27000 + i.val) →
    (table.lookup (27000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk135 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 27000 27200 :=
  FiniteIntervals.of_fin 27000 200 complete_chunk135

lemma complete_chunk136 : ∀ i : Fin 200, Compatible (27200 + i.val) →
    (table.lookup (27200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk136 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 27200 27400 :=
  FiniteIntervals.of_fin 27200 200 complete_chunk136

lemma complete_chunk137 : ∀ i : Fin 200, Compatible (27400 + i.val) →
    (table.lookup (27400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk137 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 27400 27600 :=
  FiniteIntervals.of_fin 27400 200 complete_chunk137

lemma complete_chunk138 : ∀ i : Fin 200, Compatible (27600 + i.val) →
    (table.lookup (27600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk138 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 27600 27800 :=
  FiniteIntervals.of_fin 27600 200 complete_chunk138

lemma complete_chunk139 : ∀ i : Fin 200, Compatible (27800 + i.val) →
    (table.lookup (27800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk139 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 27800 28000 :=
  FiniteIntervals.of_fin 27800 200 complete_chunk139

#print axioms interval_chunk130
end Erdos184Work.PureFiveFilter3
