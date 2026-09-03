import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2160 : ∀ i : Fin 200, Compatible (432000 + i.val) →
    (table.lookup (432000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 432000 432200 :=
  FiniteIntervals.of_fin 432000 200 complete_chunk2160

lemma complete_chunk2161 : ∀ i : Fin 200, Compatible (432200 + i.val) →
    (table.lookup (432200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 432200 432400 :=
  FiniteIntervals.of_fin 432200 200 complete_chunk2161

lemma complete_chunk2162 : ∀ i : Fin 200, Compatible (432400 + i.val) →
    (table.lookup (432400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 432400 432600 :=
  FiniteIntervals.of_fin 432400 200 complete_chunk2162

lemma complete_chunk2163 : ∀ i : Fin 200, Compatible (432600 + i.val) →
    (table.lookup (432600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 432600 432800 :=
  FiniteIntervals.of_fin 432600 200 complete_chunk2163

lemma complete_chunk2164 : ∀ i : Fin 200, Compatible (432800 + i.val) →
    (table.lookup (432800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 432800 433000 :=
  FiniteIntervals.of_fin 432800 200 complete_chunk2164

lemma complete_chunk2165 : ∀ i : Fin 200, Compatible (433000 + i.val) →
    (table.lookup (433000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 433000 433200 :=
  FiniteIntervals.of_fin 433000 200 complete_chunk2165

lemma complete_chunk2166 : ∀ i : Fin 200, Compatible (433200 + i.val) →
    (table.lookup (433200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 433200 433400 :=
  FiniteIntervals.of_fin 433200 200 complete_chunk2166

lemma complete_chunk2167 : ∀ i : Fin 200, Compatible (433400 + i.val) →
    (table.lookup (433400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 433400 433600 :=
  FiniteIntervals.of_fin 433400 200 complete_chunk2167

lemma complete_chunk2168 : ∀ i : Fin 200, Compatible (433600 + i.val) →
    (table.lookup (433600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 433600 433800 :=
  FiniteIntervals.of_fin 433600 200 complete_chunk2168

lemma complete_chunk2169 : ∀ i : Fin 200, Compatible (433800 + i.val) →
    (table.lookup (433800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 433800 434000 :=
  FiniteIntervals.of_fin 433800 200 complete_chunk2169

#print axioms interval_chunk2160
end Erdos184Work.PureFiveFilter4
