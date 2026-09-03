import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk940 : ∀ i : Fin 200, Compatible (188000 + i.val) →
    (table.lookup (188000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk940 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 188000 188200 :=
  FiniteIntervals.of_fin 188000 200 complete_chunk940

lemma complete_chunk941 : ∀ i : Fin 200, Compatible (188200 + i.val) →
    (table.lookup (188200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk941 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 188200 188400 :=
  FiniteIntervals.of_fin 188200 200 complete_chunk941

lemma complete_chunk942 : ∀ i : Fin 200, Compatible (188400 + i.val) →
    (table.lookup (188400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk942 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 188400 188600 :=
  FiniteIntervals.of_fin 188400 200 complete_chunk942

lemma complete_chunk943 : ∀ i : Fin 200, Compatible (188600 + i.val) →
    (table.lookup (188600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk943 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 188600 188800 :=
  FiniteIntervals.of_fin 188600 200 complete_chunk943

lemma complete_chunk944 : ∀ i : Fin 200, Compatible (188800 + i.val) →
    (table.lookup (188800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk944 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 188800 189000 :=
  FiniteIntervals.of_fin 188800 200 complete_chunk944

lemma complete_chunk945 : ∀ i : Fin 200, Compatible (189000 + i.val) →
    (table.lookup (189000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk945 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 189000 189200 :=
  FiniteIntervals.of_fin 189000 200 complete_chunk945

lemma complete_chunk946 : ∀ i : Fin 200, Compatible (189200 + i.val) →
    (table.lookup (189200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk946 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 189200 189400 :=
  FiniteIntervals.of_fin 189200 200 complete_chunk946

lemma complete_chunk947 : ∀ i : Fin 200, Compatible (189400 + i.val) →
    (table.lookup (189400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk947 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 189400 189600 :=
  FiniteIntervals.of_fin 189400 200 complete_chunk947

lemma complete_chunk948 : ∀ i : Fin 200, Compatible (189600 + i.val) →
    (table.lookup (189600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk948 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 189600 189800 :=
  FiniteIntervals.of_fin 189600 200 complete_chunk948

lemma complete_chunk949 : ∀ i : Fin 200, Compatible (189800 + i.val) →
    (table.lookup (189800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk949 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 189800 190000 :=
  FiniteIntervals.of_fin 189800 200 complete_chunk949

#print axioms interval_chunk940
end Erdos184Work.PureFiveFilter4
