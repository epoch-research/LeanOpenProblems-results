import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3760 : ∀ i : Fin 200, Compatible (752000 + i.val) →
    (table.lookup (752000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3760 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 752000 752200 :=
  FiniteIntervals.of_fin 752000 200 complete_chunk3760

lemma complete_chunk3761 : ∀ i : Fin 200, Compatible (752200 + i.val) →
    (table.lookup (752200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3761 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 752200 752400 :=
  FiniteIntervals.of_fin 752200 200 complete_chunk3761

lemma complete_chunk3762 : ∀ i : Fin 200, Compatible (752400 + i.val) →
    (table.lookup (752400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3762 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 752400 752600 :=
  FiniteIntervals.of_fin 752400 200 complete_chunk3762

lemma complete_chunk3763 : ∀ i : Fin 200, Compatible (752600 + i.val) →
    (table.lookup (752600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3763 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 752600 752800 :=
  FiniteIntervals.of_fin 752600 200 complete_chunk3763

lemma complete_chunk3764 : ∀ i : Fin 200, Compatible (752800 + i.val) →
    (table.lookup (752800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3764 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 752800 753000 :=
  FiniteIntervals.of_fin 752800 200 complete_chunk3764

lemma complete_chunk3765 : ∀ i : Fin 200, Compatible (753000 + i.val) →
    (table.lookup (753000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3765 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 753000 753200 :=
  FiniteIntervals.of_fin 753000 200 complete_chunk3765

lemma complete_chunk3766 : ∀ i : Fin 200, Compatible (753200 + i.val) →
    (table.lookup (753200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3766 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 753200 753400 :=
  FiniteIntervals.of_fin 753200 200 complete_chunk3766

lemma complete_chunk3767 : ∀ i : Fin 200, Compatible (753400 + i.val) →
    (table.lookup (753400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3767 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 753400 753600 :=
  FiniteIntervals.of_fin 753400 200 complete_chunk3767

lemma complete_chunk3768 : ∀ i : Fin 200, Compatible (753600 + i.val) →
    (table.lookup (753600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3768 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 753600 753800 :=
  FiniteIntervals.of_fin 753600 200 complete_chunk3768

lemma complete_chunk3769 : ∀ i : Fin 200, Compatible (753800 + i.val) →
    (table.lookup (753800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3769 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 753800 754000 :=
  FiniteIntervals.of_fin 753800 200 complete_chunk3769

#print axioms interval_chunk3760
end Erdos184Work.PureFiveFilter4
