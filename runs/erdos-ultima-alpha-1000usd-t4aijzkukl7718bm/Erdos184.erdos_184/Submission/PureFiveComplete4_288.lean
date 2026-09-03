import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2880 : ∀ i : Fin 200, Compatible (576000 + i.val) →
    (table.lookup (576000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2880 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 576000 576200 :=
  FiniteIntervals.of_fin 576000 200 complete_chunk2880

lemma complete_chunk2881 : ∀ i : Fin 200, Compatible (576200 + i.val) →
    (table.lookup (576200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2881 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 576200 576400 :=
  FiniteIntervals.of_fin 576200 200 complete_chunk2881

lemma complete_chunk2882 : ∀ i : Fin 200, Compatible (576400 + i.val) →
    (table.lookup (576400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2882 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 576400 576600 :=
  FiniteIntervals.of_fin 576400 200 complete_chunk2882

lemma complete_chunk2883 : ∀ i : Fin 200, Compatible (576600 + i.val) →
    (table.lookup (576600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2883 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 576600 576800 :=
  FiniteIntervals.of_fin 576600 200 complete_chunk2883

lemma complete_chunk2884 : ∀ i : Fin 200, Compatible (576800 + i.val) →
    (table.lookup (576800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2884 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 576800 577000 :=
  FiniteIntervals.of_fin 576800 200 complete_chunk2884

lemma complete_chunk2885 : ∀ i : Fin 200, Compatible (577000 + i.val) →
    (table.lookup (577000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2885 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 577000 577200 :=
  FiniteIntervals.of_fin 577000 200 complete_chunk2885

lemma complete_chunk2886 : ∀ i : Fin 200, Compatible (577200 + i.val) →
    (table.lookup (577200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2886 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 577200 577400 :=
  FiniteIntervals.of_fin 577200 200 complete_chunk2886

lemma complete_chunk2887 : ∀ i : Fin 200, Compatible (577400 + i.val) →
    (table.lookup (577400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2887 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 577400 577600 :=
  FiniteIntervals.of_fin 577400 200 complete_chunk2887

lemma complete_chunk2888 : ∀ i : Fin 200, Compatible (577600 + i.val) →
    (table.lookup (577600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2888 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 577600 577800 :=
  FiniteIntervals.of_fin 577600 200 complete_chunk2888

lemma complete_chunk2889 : ∀ i : Fin 200, Compatible (577800 + i.val) →
    (table.lookup (577800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2889 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 577800 578000 :=
  FiniteIntervals.of_fin 577800 200 complete_chunk2889

#print axioms interval_chunk2880
end Erdos184Work.PureFiveFilter4
