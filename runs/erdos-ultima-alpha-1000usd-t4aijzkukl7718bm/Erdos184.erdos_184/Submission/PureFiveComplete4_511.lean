import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5110 : ∀ i : Fin 200, Compatible (1022000 + i.val) →
    (table.lookup (1022000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1022000 1022200 :=
  FiniteIntervals.of_fin 1022000 200 complete_chunk5110

lemma complete_chunk5111 : ∀ i : Fin 200, Compatible (1022200 + i.val) →
    (table.lookup (1022200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1022200 1022400 :=
  FiniteIntervals.of_fin 1022200 200 complete_chunk5111

lemma complete_chunk5112 : ∀ i : Fin 200, Compatible (1022400 + i.val) →
    (table.lookup (1022400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1022400 1022600 :=
  FiniteIntervals.of_fin 1022400 200 complete_chunk5112

lemma complete_chunk5113 : ∀ i : Fin 200, Compatible (1022600 + i.val) →
    (table.lookup (1022600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1022600 1022800 :=
  FiniteIntervals.of_fin 1022600 200 complete_chunk5113

lemma complete_chunk5114 : ∀ i : Fin 200, Compatible (1022800 + i.val) →
    (table.lookup (1022800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1022800 1023000 :=
  FiniteIntervals.of_fin 1022800 200 complete_chunk5114

lemma complete_chunk5115 : ∀ i : Fin 200, Compatible (1023000 + i.val) →
    (table.lookup (1023000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1023000 1023200 :=
  FiniteIntervals.of_fin 1023000 200 complete_chunk5115

lemma complete_chunk5116 : ∀ i : Fin 200, Compatible (1023200 + i.val) →
    (table.lookup (1023200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1023200 1023400 :=
  FiniteIntervals.of_fin 1023200 200 complete_chunk5116

lemma complete_chunk5117 : ∀ i : Fin 200, Compatible (1023400 + i.val) →
    (table.lookup (1023400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1023400 1023600 :=
  FiniteIntervals.of_fin 1023400 200 complete_chunk5117

lemma complete_chunk5118 : ∀ i : Fin 200, Compatible (1023600 + i.val) →
    (table.lookup (1023600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1023600 1023800 :=
  FiniteIntervals.of_fin 1023600 200 complete_chunk5118

lemma complete_chunk5119 : ∀ i : Fin 200, Compatible (1023800 + i.val) →
    (table.lookup (1023800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1023800 1024000 :=
  FiniteIntervals.of_fin 1023800 200 complete_chunk5119

#print axioms interval_chunk5110
end Erdos184Work.PureFiveFilter4
