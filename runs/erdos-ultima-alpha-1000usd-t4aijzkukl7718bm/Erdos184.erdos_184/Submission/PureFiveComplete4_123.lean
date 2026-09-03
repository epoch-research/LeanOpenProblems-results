import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1230 : ∀ i : Fin 200, Compatible (246000 + i.val) →
    (table.lookup (246000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1230 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 246000 246200 :=
  FiniteIntervals.of_fin 246000 200 complete_chunk1230

lemma complete_chunk1231 : ∀ i : Fin 200, Compatible (246200 + i.val) →
    (table.lookup (246200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1231 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 246200 246400 :=
  FiniteIntervals.of_fin 246200 200 complete_chunk1231

lemma complete_chunk1232 : ∀ i : Fin 200, Compatible (246400 + i.val) →
    (table.lookup (246400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1232 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 246400 246600 :=
  FiniteIntervals.of_fin 246400 200 complete_chunk1232

lemma complete_chunk1233 : ∀ i : Fin 200, Compatible (246600 + i.val) →
    (table.lookup (246600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1233 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 246600 246800 :=
  FiniteIntervals.of_fin 246600 200 complete_chunk1233

lemma complete_chunk1234 : ∀ i : Fin 200, Compatible (246800 + i.val) →
    (table.lookup (246800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1234 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 246800 247000 :=
  FiniteIntervals.of_fin 246800 200 complete_chunk1234

lemma complete_chunk1235 : ∀ i : Fin 200, Compatible (247000 + i.val) →
    (table.lookup (247000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1235 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 247000 247200 :=
  FiniteIntervals.of_fin 247000 200 complete_chunk1235

lemma complete_chunk1236 : ∀ i : Fin 200, Compatible (247200 + i.val) →
    (table.lookup (247200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1236 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 247200 247400 :=
  FiniteIntervals.of_fin 247200 200 complete_chunk1236

lemma complete_chunk1237 : ∀ i : Fin 200, Compatible (247400 + i.val) →
    (table.lookup (247400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1237 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 247400 247600 :=
  FiniteIntervals.of_fin 247400 200 complete_chunk1237

lemma complete_chunk1238 : ∀ i : Fin 200, Compatible (247600 + i.val) →
    (table.lookup (247600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1238 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 247600 247800 :=
  FiniteIntervals.of_fin 247600 200 complete_chunk1238

lemma complete_chunk1239 : ∀ i : Fin 200, Compatible (247800 + i.val) →
    (table.lookup (247800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1239 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 247800 248000 :=
  FiniteIntervals.of_fin 247800 200 complete_chunk1239

#print axioms interval_chunk1230
end Erdos184Work.PureFiveFilter4
