import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4940 : ∀ i : Fin 200, Compatible (988000 + i.val) →
    (table.lookup (988000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4940 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 988000 988200 :=
  FiniteIntervals.of_fin 988000 200 complete_chunk4940

lemma complete_chunk4941 : ∀ i : Fin 200, Compatible (988200 + i.val) →
    (table.lookup (988200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4941 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 988200 988400 :=
  FiniteIntervals.of_fin 988200 200 complete_chunk4941

lemma complete_chunk4942 : ∀ i : Fin 200, Compatible (988400 + i.val) →
    (table.lookup (988400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4942 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 988400 988600 :=
  FiniteIntervals.of_fin 988400 200 complete_chunk4942

lemma complete_chunk4943 : ∀ i : Fin 200, Compatible (988600 + i.val) →
    (table.lookup (988600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4943 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 988600 988800 :=
  FiniteIntervals.of_fin 988600 200 complete_chunk4943

lemma complete_chunk4944 : ∀ i : Fin 200, Compatible (988800 + i.val) →
    (table.lookup (988800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4944 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 988800 989000 :=
  FiniteIntervals.of_fin 988800 200 complete_chunk4944

lemma complete_chunk4945 : ∀ i : Fin 200, Compatible (989000 + i.val) →
    (table.lookup (989000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4945 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 989000 989200 :=
  FiniteIntervals.of_fin 989000 200 complete_chunk4945

lemma complete_chunk4946 : ∀ i : Fin 200, Compatible (989200 + i.val) →
    (table.lookup (989200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4946 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 989200 989400 :=
  FiniteIntervals.of_fin 989200 200 complete_chunk4946

lemma complete_chunk4947 : ∀ i : Fin 200, Compatible (989400 + i.val) →
    (table.lookup (989400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4947 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 989400 989600 :=
  FiniteIntervals.of_fin 989400 200 complete_chunk4947

lemma complete_chunk4948 : ∀ i : Fin 200, Compatible (989600 + i.val) →
    (table.lookup (989600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4948 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 989600 989800 :=
  FiniteIntervals.of_fin 989600 200 complete_chunk4948

lemma complete_chunk4949 : ∀ i : Fin 200, Compatible (989800 + i.val) →
    (table.lookup (989800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4949 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 989800 990000 :=
  FiniteIntervals.of_fin 989800 200 complete_chunk4949

#print axioms interval_chunk4940
end Erdos184Work.PureFiveFilter4
