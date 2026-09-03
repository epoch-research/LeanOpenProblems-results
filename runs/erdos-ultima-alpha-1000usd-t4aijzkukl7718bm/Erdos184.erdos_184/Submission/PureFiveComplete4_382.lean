import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3820 : ∀ i : Fin 200, Compatible (764000 + i.val) →
    (table.lookup (764000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3820 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 764000 764200 :=
  FiniteIntervals.of_fin 764000 200 complete_chunk3820

lemma complete_chunk3821 : ∀ i : Fin 200, Compatible (764200 + i.val) →
    (table.lookup (764200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3821 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 764200 764400 :=
  FiniteIntervals.of_fin 764200 200 complete_chunk3821

lemma complete_chunk3822 : ∀ i : Fin 200, Compatible (764400 + i.val) →
    (table.lookup (764400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3822 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 764400 764600 :=
  FiniteIntervals.of_fin 764400 200 complete_chunk3822

lemma complete_chunk3823 : ∀ i : Fin 200, Compatible (764600 + i.val) →
    (table.lookup (764600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3823 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 764600 764800 :=
  FiniteIntervals.of_fin 764600 200 complete_chunk3823

lemma complete_chunk3824 : ∀ i : Fin 200, Compatible (764800 + i.val) →
    (table.lookup (764800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3824 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 764800 765000 :=
  FiniteIntervals.of_fin 764800 200 complete_chunk3824

lemma complete_chunk3825 : ∀ i : Fin 200, Compatible (765000 + i.val) →
    (table.lookup (765000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3825 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 765000 765200 :=
  FiniteIntervals.of_fin 765000 200 complete_chunk3825

lemma complete_chunk3826 : ∀ i : Fin 200, Compatible (765200 + i.val) →
    (table.lookup (765200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3826 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 765200 765400 :=
  FiniteIntervals.of_fin 765200 200 complete_chunk3826

lemma complete_chunk3827 : ∀ i : Fin 200, Compatible (765400 + i.val) →
    (table.lookup (765400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3827 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 765400 765600 :=
  FiniteIntervals.of_fin 765400 200 complete_chunk3827

lemma complete_chunk3828 : ∀ i : Fin 200, Compatible (765600 + i.val) →
    (table.lookup (765600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3828 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 765600 765800 :=
  FiniteIntervals.of_fin 765600 200 complete_chunk3828

lemma complete_chunk3829 : ∀ i : Fin 200, Compatible (765800 + i.val) →
    (table.lookup (765800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3829 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 765800 766000 :=
  FiniteIntervals.of_fin 765800 200 complete_chunk3829

#print axioms interval_chunk3820
end Erdos184Work.PureFiveFilter4
