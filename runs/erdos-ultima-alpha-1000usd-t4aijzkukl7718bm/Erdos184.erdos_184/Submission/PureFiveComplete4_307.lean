import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3070 : ∀ i : Fin 200, Compatible (614000 + i.val) →
    (table.lookup (614000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3070 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 614000 614200 :=
  FiniteIntervals.of_fin 614000 200 complete_chunk3070

lemma complete_chunk3071 : ∀ i : Fin 200, Compatible (614200 + i.val) →
    (table.lookup (614200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3071 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 614200 614400 :=
  FiniteIntervals.of_fin 614200 200 complete_chunk3071

lemma complete_chunk3072 : ∀ i : Fin 200, Compatible (614400 + i.val) →
    (table.lookup (614400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3072 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 614400 614600 :=
  FiniteIntervals.of_fin 614400 200 complete_chunk3072

lemma complete_chunk3073 : ∀ i : Fin 200, Compatible (614600 + i.val) →
    (table.lookup (614600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3073 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 614600 614800 :=
  FiniteIntervals.of_fin 614600 200 complete_chunk3073

lemma complete_chunk3074 : ∀ i : Fin 200, Compatible (614800 + i.val) →
    (table.lookup (614800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3074 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 614800 615000 :=
  FiniteIntervals.of_fin 614800 200 complete_chunk3074

lemma complete_chunk3075 : ∀ i : Fin 200, Compatible (615000 + i.val) →
    (table.lookup (615000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3075 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 615000 615200 :=
  FiniteIntervals.of_fin 615000 200 complete_chunk3075

lemma complete_chunk3076 : ∀ i : Fin 200, Compatible (615200 + i.val) →
    (table.lookup (615200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3076 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 615200 615400 :=
  FiniteIntervals.of_fin 615200 200 complete_chunk3076

lemma complete_chunk3077 : ∀ i : Fin 200, Compatible (615400 + i.val) →
    (table.lookup (615400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3077 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 615400 615600 :=
  FiniteIntervals.of_fin 615400 200 complete_chunk3077

lemma complete_chunk3078 : ∀ i : Fin 200, Compatible (615600 + i.val) →
    (table.lookup (615600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3078 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 615600 615800 :=
  FiniteIntervals.of_fin 615600 200 complete_chunk3078

lemma complete_chunk3079 : ∀ i : Fin 200, Compatible (615800 + i.val) →
    (table.lookup (615800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3079 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 615800 616000 :=
  FiniteIntervals.of_fin 615800 200 complete_chunk3079

#print axioms interval_chunk3070
end Erdos184Work.PureFiveFilter4
