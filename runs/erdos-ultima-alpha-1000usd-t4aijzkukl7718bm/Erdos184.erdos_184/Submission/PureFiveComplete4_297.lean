import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2970 : ∀ i : Fin 200, Compatible (594000 + i.val) →
    (table.lookup (594000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2970 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 594000 594200 :=
  FiniteIntervals.of_fin 594000 200 complete_chunk2970

lemma complete_chunk2971 : ∀ i : Fin 200, Compatible (594200 + i.val) →
    (table.lookup (594200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2971 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 594200 594400 :=
  FiniteIntervals.of_fin 594200 200 complete_chunk2971

lemma complete_chunk2972 : ∀ i : Fin 200, Compatible (594400 + i.val) →
    (table.lookup (594400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2972 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 594400 594600 :=
  FiniteIntervals.of_fin 594400 200 complete_chunk2972

lemma complete_chunk2973 : ∀ i : Fin 200, Compatible (594600 + i.val) →
    (table.lookup (594600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2973 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 594600 594800 :=
  FiniteIntervals.of_fin 594600 200 complete_chunk2973

lemma complete_chunk2974 : ∀ i : Fin 200, Compatible (594800 + i.val) →
    (table.lookup (594800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2974 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 594800 595000 :=
  FiniteIntervals.of_fin 594800 200 complete_chunk2974

lemma complete_chunk2975 : ∀ i : Fin 200, Compatible (595000 + i.val) →
    (table.lookup (595000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2975 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 595000 595200 :=
  FiniteIntervals.of_fin 595000 200 complete_chunk2975

lemma complete_chunk2976 : ∀ i : Fin 200, Compatible (595200 + i.val) →
    (table.lookup (595200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2976 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 595200 595400 :=
  FiniteIntervals.of_fin 595200 200 complete_chunk2976

lemma complete_chunk2977 : ∀ i : Fin 200, Compatible (595400 + i.val) →
    (table.lookup (595400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2977 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 595400 595600 :=
  FiniteIntervals.of_fin 595400 200 complete_chunk2977

lemma complete_chunk2978 : ∀ i : Fin 200, Compatible (595600 + i.val) →
    (table.lookup (595600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2978 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 595600 595800 :=
  FiniteIntervals.of_fin 595600 200 complete_chunk2978

lemma complete_chunk2979 : ∀ i : Fin 200, Compatible (595800 + i.val) →
    (table.lookup (595800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2979 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 595800 596000 :=
  FiniteIntervals.of_fin 595800 200 complete_chunk2979

#print axioms interval_chunk2970
end Erdos184Work.PureFiveFilter4
