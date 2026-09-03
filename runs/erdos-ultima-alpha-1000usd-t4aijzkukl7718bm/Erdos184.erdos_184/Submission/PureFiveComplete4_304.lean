import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3040 : ∀ i : Fin 200, Compatible (608000 + i.val) →
    (table.lookup (608000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3040 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 608000 608200 :=
  FiniteIntervals.of_fin 608000 200 complete_chunk3040

lemma complete_chunk3041 : ∀ i : Fin 200, Compatible (608200 + i.val) →
    (table.lookup (608200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3041 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 608200 608400 :=
  FiniteIntervals.of_fin 608200 200 complete_chunk3041

lemma complete_chunk3042 : ∀ i : Fin 200, Compatible (608400 + i.val) →
    (table.lookup (608400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3042 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 608400 608600 :=
  FiniteIntervals.of_fin 608400 200 complete_chunk3042

lemma complete_chunk3043 : ∀ i : Fin 200, Compatible (608600 + i.val) →
    (table.lookup (608600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3043 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 608600 608800 :=
  FiniteIntervals.of_fin 608600 200 complete_chunk3043

lemma complete_chunk3044 : ∀ i : Fin 200, Compatible (608800 + i.val) →
    (table.lookup (608800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3044 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 608800 609000 :=
  FiniteIntervals.of_fin 608800 200 complete_chunk3044

lemma complete_chunk3045 : ∀ i : Fin 200, Compatible (609000 + i.val) →
    (table.lookup (609000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3045 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 609000 609200 :=
  FiniteIntervals.of_fin 609000 200 complete_chunk3045

lemma complete_chunk3046 : ∀ i : Fin 200, Compatible (609200 + i.val) →
    (table.lookup (609200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3046 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 609200 609400 :=
  FiniteIntervals.of_fin 609200 200 complete_chunk3046

lemma complete_chunk3047 : ∀ i : Fin 200, Compatible (609400 + i.val) →
    (table.lookup (609400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3047 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 609400 609600 :=
  FiniteIntervals.of_fin 609400 200 complete_chunk3047

lemma complete_chunk3048 : ∀ i : Fin 200, Compatible (609600 + i.val) →
    (table.lookup (609600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3048 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 609600 609800 :=
  FiniteIntervals.of_fin 609600 200 complete_chunk3048

lemma complete_chunk3049 : ∀ i : Fin 200, Compatible (609800 + i.val) →
    (table.lookup (609800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3049 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 609800 610000 :=
  FiniteIntervals.of_fin 609800 200 complete_chunk3049

#print axioms interval_chunk3040
end Erdos184Work.PureFiveFilter4
