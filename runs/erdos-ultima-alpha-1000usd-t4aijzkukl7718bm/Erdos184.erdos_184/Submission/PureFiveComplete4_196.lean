import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1960 : ∀ i : Fin 200, Compatible (392000 + i.val) →
    (table.lookup (392000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1960 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 392000 392200 :=
  FiniteIntervals.of_fin 392000 200 complete_chunk1960

lemma complete_chunk1961 : ∀ i : Fin 200, Compatible (392200 + i.val) →
    (table.lookup (392200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1961 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 392200 392400 :=
  FiniteIntervals.of_fin 392200 200 complete_chunk1961

lemma complete_chunk1962 : ∀ i : Fin 200, Compatible (392400 + i.val) →
    (table.lookup (392400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1962 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 392400 392600 :=
  FiniteIntervals.of_fin 392400 200 complete_chunk1962

lemma complete_chunk1963 : ∀ i : Fin 200, Compatible (392600 + i.val) →
    (table.lookup (392600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1963 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 392600 392800 :=
  FiniteIntervals.of_fin 392600 200 complete_chunk1963

lemma complete_chunk1964 : ∀ i : Fin 200, Compatible (392800 + i.val) →
    (table.lookup (392800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1964 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 392800 393000 :=
  FiniteIntervals.of_fin 392800 200 complete_chunk1964

lemma complete_chunk1965 : ∀ i : Fin 200, Compatible (393000 + i.val) →
    (table.lookup (393000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1965 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 393000 393200 :=
  FiniteIntervals.of_fin 393000 200 complete_chunk1965

lemma complete_chunk1966 : ∀ i : Fin 200, Compatible (393200 + i.val) →
    (table.lookup (393200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1966 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 393200 393400 :=
  FiniteIntervals.of_fin 393200 200 complete_chunk1966

lemma complete_chunk1967 : ∀ i : Fin 200, Compatible (393400 + i.val) →
    (table.lookup (393400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1967 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 393400 393600 :=
  FiniteIntervals.of_fin 393400 200 complete_chunk1967

lemma complete_chunk1968 : ∀ i : Fin 200, Compatible (393600 + i.val) →
    (table.lookup (393600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1968 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 393600 393800 :=
  FiniteIntervals.of_fin 393600 200 complete_chunk1968

lemma complete_chunk1969 : ∀ i : Fin 200, Compatible (393800 + i.val) →
    (table.lookup (393800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1969 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 393800 394000 :=
  FiniteIntervals.of_fin 393800 200 complete_chunk1969

#print axioms interval_chunk1960
end Erdos184Work.PureFiveFilter4
