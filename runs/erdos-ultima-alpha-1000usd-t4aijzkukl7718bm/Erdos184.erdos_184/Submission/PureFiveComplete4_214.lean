import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2140 : ∀ i : Fin 200, Compatible (428000 + i.val) →
    (table.lookup (428000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2140 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 428000 428200 :=
  FiniteIntervals.of_fin 428000 200 complete_chunk2140

lemma complete_chunk2141 : ∀ i : Fin 200, Compatible (428200 + i.val) →
    (table.lookup (428200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2141 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 428200 428400 :=
  FiniteIntervals.of_fin 428200 200 complete_chunk2141

lemma complete_chunk2142 : ∀ i : Fin 200, Compatible (428400 + i.val) →
    (table.lookup (428400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2142 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 428400 428600 :=
  FiniteIntervals.of_fin 428400 200 complete_chunk2142

lemma complete_chunk2143 : ∀ i : Fin 200, Compatible (428600 + i.val) →
    (table.lookup (428600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2143 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 428600 428800 :=
  FiniteIntervals.of_fin 428600 200 complete_chunk2143

lemma complete_chunk2144 : ∀ i : Fin 200, Compatible (428800 + i.val) →
    (table.lookup (428800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2144 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 428800 429000 :=
  FiniteIntervals.of_fin 428800 200 complete_chunk2144

lemma complete_chunk2145 : ∀ i : Fin 200, Compatible (429000 + i.val) →
    (table.lookup (429000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2145 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 429000 429200 :=
  FiniteIntervals.of_fin 429000 200 complete_chunk2145

lemma complete_chunk2146 : ∀ i : Fin 200, Compatible (429200 + i.val) →
    (table.lookup (429200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2146 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 429200 429400 :=
  FiniteIntervals.of_fin 429200 200 complete_chunk2146

lemma complete_chunk2147 : ∀ i : Fin 200, Compatible (429400 + i.val) →
    (table.lookup (429400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2147 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 429400 429600 :=
  FiniteIntervals.of_fin 429400 200 complete_chunk2147

lemma complete_chunk2148 : ∀ i : Fin 200, Compatible (429600 + i.val) →
    (table.lookup (429600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2148 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 429600 429800 :=
  FiniteIntervals.of_fin 429600 200 complete_chunk2148

lemma complete_chunk2149 : ∀ i : Fin 200, Compatible (429800 + i.val) →
    (table.lookup (429800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2149 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 429800 430000 :=
  FiniteIntervals.of_fin 429800 200 complete_chunk2149

#print axioms interval_chunk2140
end Erdos184Work.PureFiveFilter4
