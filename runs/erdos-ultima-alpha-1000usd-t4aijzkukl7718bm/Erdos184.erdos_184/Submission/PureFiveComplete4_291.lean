import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2910 : ∀ i : Fin 200, Compatible (582000 + i.val) →
    (table.lookup (582000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2910 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 582000 582200 :=
  FiniteIntervals.of_fin 582000 200 complete_chunk2910

lemma complete_chunk2911 : ∀ i : Fin 200, Compatible (582200 + i.val) →
    (table.lookup (582200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2911 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 582200 582400 :=
  FiniteIntervals.of_fin 582200 200 complete_chunk2911

lemma complete_chunk2912 : ∀ i : Fin 200, Compatible (582400 + i.val) →
    (table.lookup (582400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2912 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 582400 582600 :=
  FiniteIntervals.of_fin 582400 200 complete_chunk2912

lemma complete_chunk2913 : ∀ i : Fin 200, Compatible (582600 + i.val) →
    (table.lookup (582600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2913 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 582600 582800 :=
  FiniteIntervals.of_fin 582600 200 complete_chunk2913

lemma complete_chunk2914 : ∀ i : Fin 200, Compatible (582800 + i.val) →
    (table.lookup (582800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2914 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 582800 583000 :=
  FiniteIntervals.of_fin 582800 200 complete_chunk2914

lemma complete_chunk2915 : ∀ i : Fin 200, Compatible (583000 + i.val) →
    (table.lookup (583000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2915 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 583000 583200 :=
  FiniteIntervals.of_fin 583000 200 complete_chunk2915

lemma complete_chunk2916 : ∀ i : Fin 200, Compatible (583200 + i.val) →
    (table.lookup (583200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2916 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 583200 583400 :=
  FiniteIntervals.of_fin 583200 200 complete_chunk2916

lemma complete_chunk2917 : ∀ i : Fin 200, Compatible (583400 + i.val) →
    (table.lookup (583400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2917 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 583400 583600 :=
  FiniteIntervals.of_fin 583400 200 complete_chunk2917

lemma complete_chunk2918 : ∀ i : Fin 200, Compatible (583600 + i.val) →
    (table.lookup (583600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2918 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 583600 583800 :=
  FiniteIntervals.of_fin 583600 200 complete_chunk2918

lemma complete_chunk2919 : ∀ i : Fin 200, Compatible (583800 + i.val) →
    (table.lookup (583800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2919 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 583800 584000 :=
  FiniteIntervals.of_fin 583800 200 complete_chunk2919

#print axioms interval_chunk2910
end Erdos184Work.PureFiveFilter4
