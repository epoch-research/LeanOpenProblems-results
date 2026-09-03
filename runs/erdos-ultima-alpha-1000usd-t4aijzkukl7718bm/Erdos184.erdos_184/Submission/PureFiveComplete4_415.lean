import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4150 : ∀ i : Fin 200, Compatible (830000 + i.val) →
    (table.lookup (830000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 830000 830200 :=
  FiniteIntervals.of_fin 830000 200 complete_chunk4150

lemma complete_chunk4151 : ∀ i : Fin 200, Compatible (830200 + i.val) →
    (table.lookup (830200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 830200 830400 :=
  FiniteIntervals.of_fin 830200 200 complete_chunk4151

lemma complete_chunk4152 : ∀ i : Fin 200, Compatible (830400 + i.val) →
    (table.lookup (830400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 830400 830600 :=
  FiniteIntervals.of_fin 830400 200 complete_chunk4152

lemma complete_chunk4153 : ∀ i : Fin 200, Compatible (830600 + i.val) →
    (table.lookup (830600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 830600 830800 :=
  FiniteIntervals.of_fin 830600 200 complete_chunk4153

lemma complete_chunk4154 : ∀ i : Fin 200, Compatible (830800 + i.val) →
    (table.lookup (830800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 830800 831000 :=
  FiniteIntervals.of_fin 830800 200 complete_chunk4154

lemma complete_chunk4155 : ∀ i : Fin 200, Compatible (831000 + i.val) →
    (table.lookup (831000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 831000 831200 :=
  FiniteIntervals.of_fin 831000 200 complete_chunk4155

lemma complete_chunk4156 : ∀ i : Fin 200, Compatible (831200 + i.val) →
    (table.lookup (831200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 831200 831400 :=
  FiniteIntervals.of_fin 831200 200 complete_chunk4156

lemma complete_chunk4157 : ∀ i : Fin 200, Compatible (831400 + i.val) →
    (table.lookup (831400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 831400 831600 :=
  FiniteIntervals.of_fin 831400 200 complete_chunk4157

lemma complete_chunk4158 : ∀ i : Fin 200, Compatible (831600 + i.val) →
    (table.lookup (831600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 831600 831800 :=
  FiniteIntervals.of_fin 831600 200 complete_chunk4158

lemma complete_chunk4159 : ∀ i : Fin 200, Compatible (831800 + i.val) →
    (table.lookup (831800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 831800 832000 :=
  FiniteIntervals.of_fin 831800 200 complete_chunk4159

#print axioms interval_chunk4150
end Erdos184Work.PureFiveFilter4
