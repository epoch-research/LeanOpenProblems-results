import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4140 : ∀ i : Fin 200, Compatible (828000 + i.val) →
    (table.lookup (828000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 828000 828200 :=
  FiniteIntervals.of_fin 828000 200 complete_chunk4140

lemma complete_chunk4141 : ∀ i : Fin 200, Compatible (828200 + i.val) →
    (table.lookup (828200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 828200 828400 :=
  FiniteIntervals.of_fin 828200 200 complete_chunk4141

lemma complete_chunk4142 : ∀ i : Fin 200, Compatible (828400 + i.val) →
    (table.lookup (828400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 828400 828600 :=
  FiniteIntervals.of_fin 828400 200 complete_chunk4142

lemma complete_chunk4143 : ∀ i : Fin 200, Compatible (828600 + i.val) →
    (table.lookup (828600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 828600 828800 :=
  FiniteIntervals.of_fin 828600 200 complete_chunk4143

lemma complete_chunk4144 : ∀ i : Fin 200, Compatible (828800 + i.val) →
    (table.lookup (828800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 828800 829000 :=
  FiniteIntervals.of_fin 828800 200 complete_chunk4144

lemma complete_chunk4145 : ∀ i : Fin 200, Compatible (829000 + i.val) →
    (table.lookup (829000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 829000 829200 :=
  FiniteIntervals.of_fin 829000 200 complete_chunk4145

lemma complete_chunk4146 : ∀ i : Fin 200, Compatible (829200 + i.val) →
    (table.lookup (829200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 829200 829400 :=
  FiniteIntervals.of_fin 829200 200 complete_chunk4146

lemma complete_chunk4147 : ∀ i : Fin 200, Compatible (829400 + i.val) →
    (table.lookup (829400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 829400 829600 :=
  FiniteIntervals.of_fin 829400 200 complete_chunk4147

lemma complete_chunk4148 : ∀ i : Fin 200, Compatible (829600 + i.val) →
    (table.lookup (829600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 829600 829800 :=
  FiniteIntervals.of_fin 829600 200 complete_chunk4148

lemma complete_chunk4149 : ∀ i : Fin 200, Compatible (829800 + i.val) →
    (table.lookup (829800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 829800 830000 :=
  FiniteIntervals.of_fin 829800 200 complete_chunk4149

#print axioms interval_chunk4140
end Erdos184Work.PureFiveFilter4
