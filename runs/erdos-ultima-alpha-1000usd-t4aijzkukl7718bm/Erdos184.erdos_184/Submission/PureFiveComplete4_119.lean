import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1190 : ∀ i : Fin 200, Compatible (238000 + i.val) →
    (table.lookup (238000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 238000 238200 :=
  FiniteIntervals.of_fin 238000 200 complete_chunk1190

lemma complete_chunk1191 : ∀ i : Fin 200, Compatible (238200 + i.val) →
    (table.lookup (238200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 238200 238400 :=
  FiniteIntervals.of_fin 238200 200 complete_chunk1191

lemma complete_chunk1192 : ∀ i : Fin 200, Compatible (238400 + i.val) →
    (table.lookup (238400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 238400 238600 :=
  FiniteIntervals.of_fin 238400 200 complete_chunk1192

lemma complete_chunk1193 : ∀ i : Fin 200, Compatible (238600 + i.val) →
    (table.lookup (238600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 238600 238800 :=
  FiniteIntervals.of_fin 238600 200 complete_chunk1193

lemma complete_chunk1194 : ∀ i : Fin 200, Compatible (238800 + i.val) →
    (table.lookup (238800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 238800 239000 :=
  FiniteIntervals.of_fin 238800 200 complete_chunk1194

lemma complete_chunk1195 : ∀ i : Fin 200, Compatible (239000 + i.val) →
    (table.lookup (239000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 239000 239200 :=
  FiniteIntervals.of_fin 239000 200 complete_chunk1195

lemma complete_chunk1196 : ∀ i : Fin 200, Compatible (239200 + i.val) →
    (table.lookup (239200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 239200 239400 :=
  FiniteIntervals.of_fin 239200 200 complete_chunk1196

lemma complete_chunk1197 : ∀ i : Fin 200, Compatible (239400 + i.val) →
    (table.lookup (239400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 239400 239600 :=
  FiniteIntervals.of_fin 239400 200 complete_chunk1197

lemma complete_chunk1198 : ∀ i : Fin 200, Compatible (239600 + i.val) →
    (table.lookup (239600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 239600 239800 :=
  FiniteIntervals.of_fin 239600 200 complete_chunk1198

lemma complete_chunk1199 : ∀ i : Fin 200, Compatible (239800 + i.val) →
    (table.lookup (239800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 239800 240000 :=
  FiniteIntervals.of_fin 239800 200 complete_chunk1199

#print axioms interval_chunk1190
end Erdos184Work.PureFiveFilter4
