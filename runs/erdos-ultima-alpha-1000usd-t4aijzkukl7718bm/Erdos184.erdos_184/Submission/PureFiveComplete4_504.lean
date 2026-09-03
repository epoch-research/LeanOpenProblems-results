import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5040 : ∀ i : Fin 200, Compatible (1008000 + i.val) →
    (table.lookup (1008000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5040 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1008000 1008200 :=
  FiniteIntervals.of_fin 1008000 200 complete_chunk5040

lemma complete_chunk5041 : ∀ i : Fin 200, Compatible (1008200 + i.val) →
    (table.lookup (1008200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5041 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1008200 1008400 :=
  FiniteIntervals.of_fin 1008200 200 complete_chunk5041

lemma complete_chunk5042 : ∀ i : Fin 200, Compatible (1008400 + i.val) →
    (table.lookup (1008400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5042 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1008400 1008600 :=
  FiniteIntervals.of_fin 1008400 200 complete_chunk5042

lemma complete_chunk5043 : ∀ i : Fin 200, Compatible (1008600 + i.val) →
    (table.lookup (1008600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5043 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1008600 1008800 :=
  FiniteIntervals.of_fin 1008600 200 complete_chunk5043

lemma complete_chunk5044 : ∀ i : Fin 200, Compatible (1008800 + i.val) →
    (table.lookup (1008800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5044 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1008800 1009000 :=
  FiniteIntervals.of_fin 1008800 200 complete_chunk5044

lemma complete_chunk5045 : ∀ i : Fin 200, Compatible (1009000 + i.val) →
    (table.lookup (1009000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5045 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1009000 1009200 :=
  FiniteIntervals.of_fin 1009000 200 complete_chunk5045

lemma complete_chunk5046 : ∀ i : Fin 200, Compatible (1009200 + i.val) →
    (table.lookup (1009200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5046 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1009200 1009400 :=
  FiniteIntervals.of_fin 1009200 200 complete_chunk5046

lemma complete_chunk5047 : ∀ i : Fin 200, Compatible (1009400 + i.val) →
    (table.lookup (1009400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5047 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1009400 1009600 :=
  FiniteIntervals.of_fin 1009400 200 complete_chunk5047

lemma complete_chunk5048 : ∀ i : Fin 200, Compatible (1009600 + i.val) →
    (table.lookup (1009600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5048 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1009600 1009800 :=
  FiniteIntervals.of_fin 1009600 200 complete_chunk5048

lemma complete_chunk5049 : ∀ i : Fin 200, Compatible (1009800 + i.val) →
    (table.lookup (1009800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5049 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1009800 1010000 :=
  FiniteIntervals.of_fin 1009800 200 complete_chunk5049

#print axioms interval_chunk5040
end Erdos184Work.PureFiveFilter4
