import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3880 : ∀ i : Fin 200, Compatible (776000 + i.val) →
    (table.lookup (776000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3880 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 776000 776200 :=
  FiniteIntervals.of_fin 776000 200 complete_chunk3880

lemma complete_chunk3881 : ∀ i : Fin 200, Compatible (776200 + i.val) →
    (table.lookup (776200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3881 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 776200 776400 :=
  FiniteIntervals.of_fin 776200 200 complete_chunk3881

lemma complete_chunk3882 : ∀ i : Fin 200, Compatible (776400 + i.val) →
    (table.lookup (776400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3882 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 776400 776600 :=
  FiniteIntervals.of_fin 776400 200 complete_chunk3882

lemma complete_chunk3883 : ∀ i : Fin 200, Compatible (776600 + i.val) →
    (table.lookup (776600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3883 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 776600 776800 :=
  FiniteIntervals.of_fin 776600 200 complete_chunk3883

lemma complete_chunk3884 : ∀ i : Fin 200, Compatible (776800 + i.val) →
    (table.lookup (776800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3884 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 776800 777000 :=
  FiniteIntervals.of_fin 776800 200 complete_chunk3884

lemma complete_chunk3885 : ∀ i : Fin 200, Compatible (777000 + i.val) →
    (table.lookup (777000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3885 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 777000 777200 :=
  FiniteIntervals.of_fin 777000 200 complete_chunk3885

lemma complete_chunk3886 : ∀ i : Fin 200, Compatible (777200 + i.val) →
    (table.lookup (777200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3886 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 777200 777400 :=
  FiniteIntervals.of_fin 777200 200 complete_chunk3886

lemma complete_chunk3887 : ∀ i : Fin 200, Compatible (777400 + i.val) →
    (table.lookup (777400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3887 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 777400 777600 :=
  FiniteIntervals.of_fin 777400 200 complete_chunk3887

lemma complete_chunk3888 : ∀ i : Fin 200, Compatible (777600 + i.val) →
    (table.lookup (777600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3888 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 777600 777800 :=
  FiniteIntervals.of_fin 777600 200 complete_chunk3888

lemma complete_chunk3889 : ∀ i : Fin 200, Compatible (777800 + i.val) →
    (table.lookup (777800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3889 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 777800 778000 :=
  FiniteIntervals.of_fin 777800 200 complete_chunk3889

#print axioms interval_chunk3880
end Erdos184Work.PureFiveFilter4
