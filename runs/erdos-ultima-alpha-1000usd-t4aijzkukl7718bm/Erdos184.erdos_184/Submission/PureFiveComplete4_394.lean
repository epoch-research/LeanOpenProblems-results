import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3940 : ∀ i : Fin 200, Compatible (788000 + i.val) →
    (table.lookup (788000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3940 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 788000 788200 :=
  FiniteIntervals.of_fin 788000 200 complete_chunk3940

lemma complete_chunk3941 : ∀ i : Fin 200, Compatible (788200 + i.val) →
    (table.lookup (788200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3941 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 788200 788400 :=
  FiniteIntervals.of_fin 788200 200 complete_chunk3941

lemma complete_chunk3942 : ∀ i : Fin 200, Compatible (788400 + i.val) →
    (table.lookup (788400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3942 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 788400 788600 :=
  FiniteIntervals.of_fin 788400 200 complete_chunk3942

lemma complete_chunk3943 : ∀ i : Fin 200, Compatible (788600 + i.val) →
    (table.lookup (788600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3943 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 788600 788800 :=
  FiniteIntervals.of_fin 788600 200 complete_chunk3943

lemma complete_chunk3944 : ∀ i : Fin 200, Compatible (788800 + i.val) →
    (table.lookup (788800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3944 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 788800 789000 :=
  FiniteIntervals.of_fin 788800 200 complete_chunk3944

lemma complete_chunk3945 : ∀ i : Fin 200, Compatible (789000 + i.val) →
    (table.lookup (789000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3945 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 789000 789200 :=
  FiniteIntervals.of_fin 789000 200 complete_chunk3945

lemma complete_chunk3946 : ∀ i : Fin 200, Compatible (789200 + i.val) →
    (table.lookup (789200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3946 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 789200 789400 :=
  FiniteIntervals.of_fin 789200 200 complete_chunk3946

lemma complete_chunk3947 : ∀ i : Fin 200, Compatible (789400 + i.val) →
    (table.lookup (789400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3947 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 789400 789600 :=
  FiniteIntervals.of_fin 789400 200 complete_chunk3947

lemma complete_chunk3948 : ∀ i : Fin 200, Compatible (789600 + i.val) →
    (table.lookup (789600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3948 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 789600 789800 :=
  FiniteIntervals.of_fin 789600 200 complete_chunk3948

lemma complete_chunk3949 : ∀ i : Fin 200, Compatible (789800 + i.val) →
    (table.lookup (789800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3949 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 789800 790000 :=
  FiniteIntervals.of_fin 789800 200 complete_chunk3949

#print axioms interval_chunk3940
end Erdos184Work.PureFiveFilter4
