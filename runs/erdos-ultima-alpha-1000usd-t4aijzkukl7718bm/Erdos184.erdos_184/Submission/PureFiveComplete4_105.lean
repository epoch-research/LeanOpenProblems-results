import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1050 : ∀ i : Fin 200, Compatible (210000 + i.val) →
    (table.lookup (210000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1050 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 210000 210200 :=
  FiniteIntervals.of_fin 210000 200 complete_chunk1050

lemma complete_chunk1051 : ∀ i : Fin 200, Compatible (210200 + i.val) →
    (table.lookup (210200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1051 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 210200 210400 :=
  FiniteIntervals.of_fin 210200 200 complete_chunk1051

lemma complete_chunk1052 : ∀ i : Fin 200, Compatible (210400 + i.val) →
    (table.lookup (210400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1052 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 210400 210600 :=
  FiniteIntervals.of_fin 210400 200 complete_chunk1052

lemma complete_chunk1053 : ∀ i : Fin 200, Compatible (210600 + i.val) →
    (table.lookup (210600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1053 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 210600 210800 :=
  FiniteIntervals.of_fin 210600 200 complete_chunk1053

lemma complete_chunk1054 : ∀ i : Fin 200, Compatible (210800 + i.val) →
    (table.lookup (210800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1054 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 210800 211000 :=
  FiniteIntervals.of_fin 210800 200 complete_chunk1054

lemma complete_chunk1055 : ∀ i : Fin 200, Compatible (211000 + i.val) →
    (table.lookup (211000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1055 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 211000 211200 :=
  FiniteIntervals.of_fin 211000 200 complete_chunk1055

lemma complete_chunk1056 : ∀ i : Fin 200, Compatible (211200 + i.val) →
    (table.lookup (211200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1056 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 211200 211400 :=
  FiniteIntervals.of_fin 211200 200 complete_chunk1056

lemma complete_chunk1057 : ∀ i : Fin 200, Compatible (211400 + i.val) →
    (table.lookup (211400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1057 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 211400 211600 :=
  FiniteIntervals.of_fin 211400 200 complete_chunk1057

lemma complete_chunk1058 : ∀ i : Fin 200, Compatible (211600 + i.val) →
    (table.lookup (211600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1058 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 211600 211800 :=
  FiniteIntervals.of_fin 211600 200 complete_chunk1058

lemma complete_chunk1059 : ∀ i : Fin 200, Compatible (211800 + i.val) →
    (table.lookup (211800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1059 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 211800 212000 :=
  FiniteIntervals.of_fin 211800 200 complete_chunk1059

#print axioms interval_chunk1050
end Erdos184Work.PureFiveFilter4
