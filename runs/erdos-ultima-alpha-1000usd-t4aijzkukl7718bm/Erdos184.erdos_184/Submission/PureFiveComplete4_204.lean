import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2040 : ∀ i : Fin 200, Compatible (408000 + i.val) →
    (table.lookup (408000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2040 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 408000 408200 :=
  FiniteIntervals.of_fin 408000 200 complete_chunk2040

lemma complete_chunk2041 : ∀ i : Fin 200, Compatible (408200 + i.val) →
    (table.lookup (408200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2041 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 408200 408400 :=
  FiniteIntervals.of_fin 408200 200 complete_chunk2041

lemma complete_chunk2042 : ∀ i : Fin 200, Compatible (408400 + i.val) →
    (table.lookup (408400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2042 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 408400 408600 :=
  FiniteIntervals.of_fin 408400 200 complete_chunk2042

lemma complete_chunk2043 : ∀ i : Fin 200, Compatible (408600 + i.val) →
    (table.lookup (408600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2043 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 408600 408800 :=
  FiniteIntervals.of_fin 408600 200 complete_chunk2043

lemma complete_chunk2044 : ∀ i : Fin 200, Compatible (408800 + i.val) →
    (table.lookup (408800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2044 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 408800 409000 :=
  FiniteIntervals.of_fin 408800 200 complete_chunk2044

lemma complete_chunk2045 : ∀ i : Fin 200, Compatible (409000 + i.val) →
    (table.lookup (409000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2045 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 409000 409200 :=
  FiniteIntervals.of_fin 409000 200 complete_chunk2045

lemma complete_chunk2046 : ∀ i : Fin 200, Compatible (409200 + i.val) →
    (table.lookup (409200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2046 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 409200 409400 :=
  FiniteIntervals.of_fin 409200 200 complete_chunk2046

lemma complete_chunk2047 : ∀ i : Fin 200, Compatible (409400 + i.val) →
    (table.lookup (409400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2047 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 409400 409600 :=
  FiniteIntervals.of_fin 409400 200 complete_chunk2047

lemma complete_chunk2048 : ∀ i : Fin 200, Compatible (409600 + i.val) →
    (table.lookup (409600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2048 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 409600 409800 :=
  FiniteIntervals.of_fin 409600 200 complete_chunk2048

lemma complete_chunk2049 : ∀ i : Fin 200, Compatible (409800 + i.val) →
    (table.lookup (409800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2049 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 409800 410000 :=
  FiniteIntervals.of_fin 409800 200 complete_chunk2049

#print axioms interval_chunk2040
end Erdos184Work.PureFiveFilter4
