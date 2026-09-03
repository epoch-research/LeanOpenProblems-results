import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3890 : ∀ i : Fin 200, Compatible (778000 + i.val) →
    (table.lookup (778000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3890 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 778000 778200 :=
  FiniteIntervals.of_fin 778000 200 complete_chunk3890

lemma complete_chunk3891 : ∀ i : Fin 200, Compatible (778200 + i.val) →
    (table.lookup (778200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3891 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 778200 778400 :=
  FiniteIntervals.of_fin 778200 200 complete_chunk3891

lemma complete_chunk3892 : ∀ i : Fin 200, Compatible (778400 + i.val) →
    (table.lookup (778400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3892 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 778400 778600 :=
  FiniteIntervals.of_fin 778400 200 complete_chunk3892

lemma complete_chunk3893 : ∀ i : Fin 200, Compatible (778600 + i.val) →
    (table.lookup (778600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3893 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 778600 778800 :=
  FiniteIntervals.of_fin 778600 200 complete_chunk3893

lemma complete_chunk3894 : ∀ i : Fin 200, Compatible (778800 + i.val) →
    (table.lookup (778800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3894 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 778800 779000 :=
  FiniteIntervals.of_fin 778800 200 complete_chunk3894

lemma complete_chunk3895 : ∀ i : Fin 200, Compatible (779000 + i.val) →
    (table.lookup (779000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3895 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 779000 779200 :=
  FiniteIntervals.of_fin 779000 200 complete_chunk3895

lemma complete_chunk3896 : ∀ i : Fin 200, Compatible (779200 + i.val) →
    (table.lookup (779200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3896 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 779200 779400 :=
  FiniteIntervals.of_fin 779200 200 complete_chunk3896

lemma complete_chunk3897 : ∀ i : Fin 200, Compatible (779400 + i.val) →
    (table.lookup (779400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3897 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 779400 779600 :=
  FiniteIntervals.of_fin 779400 200 complete_chunk3897

lemma complete_chunk3898 : ∀ i : Fin 200, Compatible (779600 + i.val) →
    (table.lookup (779600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3898 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 779600 779800 :=
  FiniteIntervals.of_fin 779600 200 complete_chunk3898

lemma complete_chunk3899 : ∀ i : Fin 200, Compatible (779800 + i.val) →
    (table.lookup (779800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3899 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 779800 780000 :=
  FiniteIntervals.of_fin 779800 200 complete_chunk3899

#print axioms interval_chunk3890
end Erdos184Work.PureFiveFilter4
