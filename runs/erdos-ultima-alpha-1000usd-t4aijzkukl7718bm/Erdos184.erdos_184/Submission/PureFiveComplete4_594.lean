import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5940 : ∀ i : Fin 200, Compatible (1188000 + i.val) →
    (table.lookup (1188000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5940 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1188000 1188200 :=
  FiniteIntervals.of_fin 1188000 200 complete_chunk5940

lemma complete_chunk5941 : ∀ i : Fin 200, Compatible (1188200 + i.val) →
    (table.lookup (1188200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5941 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1188200 1188400 :=
  FiniteIntervals.of_fin 1188200 200 complete_chunk5941

lemma complete_chunk5942 : ∀ i : Fin 200, Compatible (1188400 + i.val) →
    (table.lookup (1188400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5942 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1188400 1188600 :=
  FiniteIntervals.of_fin 1188400 200 complete_chunk5942

lemma complete_chunk5943 : ∀ i : Fin 200, Compatible (1188600 + i.val) →
    (table.lookup (1188600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5943 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1188600 1188800 :=
  FiniteIntervals.of_fin 1188600 200 complete_chunk5943

lemma complete_chunk5944 : ∀ i : Fin 200, Compatible (1188800 + i.val) →
    (table.lookup (1188800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5944 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1188800 1189000 :=
  FiniteIntervals.of_fin 1188800 200 complete_chunk5944

lemma complete_chunk5945 : ∀ i : Fin 200, Compatible (1189000 + i.val) →
    (table.lookup (1189000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5945 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1189000 1189200 :=
  FiniteIntervals.of_fin 1189000 200 complete_chunk5945

lemma complete_chunk5946 : ∀ i : Fin 200, Compatible (1189200 + i.val) →
    (table.lookup (1189200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5946 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1189200 1189400 :=
  FiniteIntervals.of_fin 1189200 200 complete_chunk5946

lemma complete_chunk5947 : ∀ i : Fin 200, Compatible (1189400 + i.val) →
    (table.lookup (1189400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5947 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1189400 1189600 :=
  FiniteIntervals.of_fin 1189400 200 complete_chunk5947

lemma complete_chunk5948 : ∀ i : Fin 200, Compatible (1189600 + i.val) →
    (table.lookup (1189600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5948 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1189600 1189800 :=
  FiniteIntervals.of_fin 1189600 200 complete_chunk5948

lemma complete_chunk5949 : ∀ i : Fin 200, Compatible (1189800 + i.val) →
    (table.lookup (1189800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5949 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1189800 1190000 :=
  FiniteIntervals.of_fin 1189800 200 complete_chunk5949

#print axioms interval_chunk5940
end Erdos184Work.PureFiveFilter4
