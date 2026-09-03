import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6050 : ∀ i : Fin 200, Compatible (1210000 + i.val) →
    (table.lookup (1210000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6050 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1210000 1210200 :=
  FiniteIntervals.of_fin 1210000 200 complete_chunk6050

lemma complete_chunk6051 : ∀ i : Fin 200, Compatible (1210200 + i.val) →
    (table.lookup (1210200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6051 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1210200 1210400 :=
  FiniteIntervals.of_fin 1210200 200 complete_chunk6051

lemma complete_chunk6052 : ∀ i : Fin 200, Compatible (1210400 + i.val) →
    (table.lookup (1210400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6052 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1210400 1210600 :=
  FiniteIntervals.of_fin 1210400 200 complete_chunk6052

lemma complete_chunk6053 : ∀ i : Fin 200, Compatible (1210600 + i.val) →
    (table.lookup (1210600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6053 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1210600 1210800 :=
  FiniteIntervals.of_fin 1210600 200 complete_chunk6053

lemma complete_chunk6054 : ∀ i : Fin 200, Compatible (1210800 + i.val) →
    (table.lookup (1210800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6054 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1210800 1211000 :=
  FiniteIntervals.of_fin 1210800 200 complete_chunk6054

lemma complete_chunk6055 : ∀ i : Fin 200, Compatible (1211000 + i.val) →
    (table.lookup (1211000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6055 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1211000 1211200 :=
  FiniteIntervals.of_fin 1211000 200 complete_chunk6055

lemma complete_chunk6056 : ∀ i : Fin 200, Compatible (1211200 + i.val) →
    (table.lookup (1211200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6056 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1211200 1211400 :=
  FiniteIntervals.of_fin 1211200 200 complete_chunk6056

lemma complete_chunk6057 : ∀ i : Fin 200, Compatible (1211400 + i.val) →
    (table.lookup (1211400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6057 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1211400 1211600 :=
  FiniteIntervals.of_fin 1211400 200 complete_chunk6057

lemma complete_chunk6058 : ∀ i : Fin 200, Compatible (1211600 + i.val) →
    (table.lookup (1211600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6058 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1211600 1211800 :=
  FiniteIntervals.of_fin 1211600 200 complete_chunk6058

lemma complete_chunk6059 : ∀ i : Fin 200, Compatible (1211800 + i.val) →
    (table.lookup (1211800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6059 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1211800 1212000 :=
  FiniteIntervals.of_fin 1211800 200 complete_chunk6059

#print axioms interval_chunk6050
end Erdos184Work.PureFiveFilter4
