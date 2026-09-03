import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk6190 : ∀ i : Fin 200, Compatible (1238000 + i.val) →
    (table.lookup (1238000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1238000 1238200 :=
  FiniteIntervals.of_fin 1238000 200 complete_chunk6190

lemma complete_chunk6191 : ∀ i : Fin 200, Compatible (1238200 + i.val) →
    (table.lookup (1238200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1238200 1238400 :=
  FiniteIntervals.of_fin 1238200 200 complete_chunk6191

lemma complete_chunk6192 : ∀ i : Fin 200, Compatible (1238400 + i.val) →
    (table.lookup (1238400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1238400 1238600 :=
  FiniteIntervals.of_fin 1238400 200 complete_chunk6192

lemma complete_chunk6193 : ∀ i : Fin 200, Compatible (1238600 + i.val) →
    (table.lookup (1238600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1238600 1238800 :=
  FiniteIntervals.of_fin 1238600 200 complete_chunk6193

lemma complete_chunk6194 : ∀ i : Fin 200, Compatible (1238800 + i.val) →
    (table.lookup (1238800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1238800 1239000 :=
  FiniteIntervals.of_fin 1238800 200 complete_chunk6194

lemma complete_chunk6195 : ∀ i : Fin 200, Compatible (1239000 + i.val) →
    (table.lookup (1239000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1239000 1239200 :=
  FiniteIntervals.of_fin 1239000 200 complete_chunk6195

lemma complete_chunk6196 : ∀ i : Fin 200, Compatible (1239200 + i.val) →
    (table.lookup (1239200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1239200 1239400 :=
  FiniteIntervals.of_fin 1239200 200 complete_chunk6196

lemma complete_chunk6197 : ∀ i : Fin 200, Compatible (1239400 + i.val) →
    (table.lookup (1239400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1239400 1239600 :=
  FiniteIntervals.of_fin 1239400 200 complete_chunk6197

lemma complete_chunk6198 : ∀ i : Fin 200, Compatible (1239600 + i.val) →
    (table.lookup (1239600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1239600 1239800 :=
  FiniteIntervals.of_fin 1239600 200 complete_chunk6198

lemma complete_chunk6199 : ∀ i : Fin 200, Compatible (1239800 + i.val) →
    (table.lookup (1239800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk6199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1239800 1240000 :=
  FiniteIntervals.of_fin 1239800 200 complete_chunk6199

#print axioms interval_chunk6190
end Erdos184Work.PureFiveFilter4
