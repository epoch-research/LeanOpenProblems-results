import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2200 : ∀ i : Fin 200, Compatible (440000 + i.val) →
    (table.lookup (440000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 440000 440200 :=
  FiniteIntervals.of_fin 440000 200 complete_chunk2200

lemma complete_chunk2201 : ∀ i : Fin 200, Compatible (440200 + i.val) →
    (table.lookup (440200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 440200 440400 :=
  FiniteIntervals.of_fin 440200 200 complete_chunk2201

lemma complete_chunk2202 : ∀ i : Fin 200, Compatible (440400 + i.val) →
    (table.lookup (440400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 440400 440600 :=
  FiniteIntervals.of_fin 440400 200 complete_chunk2202

lemma complete_chunk2203 : ∀ i : Fin 200, Compatible (440600 + i.val) →
    (table.lookup (440600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 440600 440800 :=
  FiniteIntervals.of_fin 440600 200 complete_chunk2203

lemma complete_chunk2204 : ∀ i : Fin 200, Compatible (440800 + i.val) →
    (table.lookup (440800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 440800 441000 :=
  FiniteIntervals.of_fin 440800 200 complete_chunk2204

lemma complete_chunk2205 : ∀ i : Fin 200, Compatible (441000 + i.val) →
    (table.lookup (441000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 441000 441200 :=
  FiniteIntervals.of_fin 441000 200 complete_chunk2205

lemma complete_chunk2206 : ∀ i : Fin 200, Compatible (441200 + i.val) →
    (table.lookup (441200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 441200 441400 :=
  FiniteIntervals.of_fin 441200 200 complete_chunk2206

lemma complete_chunk2207 : ∀ i : Fin 200, Compatible (441400 + i.val) →
    (table.lookup (441400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 441400 441600 :=
  FiniteIntervals.of_fin 441400 200 complete_chunk2207

lemma complete_chunk2208 : ∀ i : Fin 200, Compatible (441600 + i.val) →
    (table.lookup (441600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 441600 441800 :=
  FiniteIntervals.of_fin 441600 200 complete_chunk2208

lemma complete_chunk2209 : ∀ i : Fin 200, Compatible (441800 + i.val) →
    (table.lookup (441800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 441800 442000 :=
  FiniteIntervals.of_fin 441800 200 complete_chunk2209

#print axioms interval_chunk2200
end Erdos184Work.PureFiveFilter4
