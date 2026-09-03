import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk110 : ∀ i : Fin 200, Compatible (22000 + i.val) →
    (table.lookup (22000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 22000 22200 :=
  FiniteIntervals.of_fin 22000 200 complete_chunk110

lemma complete_chunk111 : ∀ i : Fin 200, Compatible (22200 + i.val) →
    (table.lookup (22200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 22200 22400 :=
  FiniteIntervals.of_fin 22200 200 complete_chunk111

lemma complete_chunk112 : ∀ i : Fin 200, Compatible (22400 + i.val) →
    (table.lookup (22400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 22400 22600 :=
  FiniteIntervals.of_fin 22400 200 complete_chunk112

lemma complete_chunk113 : ∀ i : Fin 200, Compatible (22600 + i.val) →
    (table.lookup (22600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 22600 22800 :=
  FiniteIntervals.of_fin 22600 200 complete_chunk113

lemma complete_chunk114 : ∀ i : Fin 200, Compatible (22800 + i.val) →
    (table.lookup (22800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 22800 23000 :=
  FiniteIntervals.of_fin 22800 200 complete_chunk114

lemma complete_chunk115 : ∀ i : Fin 200, Compatible (23000 + i.val) →
    (table.lookup (23000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 23000 23200 :=
  FiniteIntervals.of_fin 23000 200 complete_chunk115

lemma complete_chunk116 : ∀ i : Fin 200, Compatible (23200 + i.val) →
    (table.lookup (23200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 23200 23400 :=
  FiniteIntervals.of_fin 23200 200 complete_chunk116

lemma complete_chunk117 : ∀ i : Fin 200, Compatible (23400 + i.val) →
    (table.lookup (23400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 23400 23600 :=
  FiniteIntervals.of_fin 23400 200 complete_chunk117

lemma complete_chunk118 : ∀ i : Fin 200, Compatible (23600 + i.val) →
    (table.lookup (23600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 23600 23800 :=
  FiniteIntervals.of_fin 23600 200 complete_chunk118

lemma complete_chunk119 : ∀ i : Fin 200, Compatible (23800 + i.val) →
    (table.lookup (23800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 23800 24000 :=
  FiniteIntervals.of_fin 23800 200 complete_chunk119

#print axioms interval_chunk110
end Erdos184Work.PureFiveFilter3
