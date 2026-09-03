import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4190 : ∀ i : Fin 200, Compatible (838000 + i.val) →
    (table.lookup (838000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 838000 838200 :=
  FiniteIntervals.of_fin 838000 200 complete_chunk4190

lemma complete_chunk4191 : ∀ i : Fin 200, Compatible (838200 + i.val) →
    (table.lookup (838200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 838200 838400 :=
  FiniteIntervals.of_fin 838200 200 complete_chunk4191

lemma complete_chunk4192 : ∀ i : Fin 200, Compatible (838400 + i.val) →
    (table.lookup (838400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 838400 838600 :=
  FiniteIntervals.of_fin 838400 200 complete_chunk4192

lemma complete_chunk4193 : ∀ i : Fin 200, Compatible (838600 + i.val) →
    (table.lookup (838600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 838600 838800 :=
  FiniteIntervals.of_fin 838600 200 complete_chunk4193

lemma complete_chunk4194 : ∀ i : Fin 200, Compatible (838800 + i.val) →
    (table.lookup (838800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 838800 839000 :=
  FiniteIntervals.of_fin 838800 200 complete_chunk4194

lemma complete_chunk4195 : ∀ i : Fin 200, Compatible (839000 + i.val) →
    (table.lookup (839000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 839000 839200 :=
  FiniteIntervals.of_fin 839000 200 complete_chunk4195

lemma complete_chunk4196 : ∀ i : Fin 200, Compatible (839200 + i.val) →
    (table.lookup (839200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 839200 839400 :=
  FiniteIntervals.of_fin 839200 200 complete_chunk4196

lemma complete_chunk4197 : ∀ i : Fin 200, Compatible (839400 + i.val) →
    (table.lookup (839400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 839400 839600 :=
  FiniteIntervals.of_fin 839400 200 complete_chunk4197

lemma complete_chunk4198 : ∀ i : Fin 200, Compatible (839600 + i.val) →
    (table.lookup (839600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 839600 839800 :=
  FiniteIntervals.of_fin 839600 200 complete_chunk4198

lemma complete_chunk4199 : ∀ i : Fin 200, Compatible (839800 + i.val) →
    (table.lookup (839800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 839800 840000 :=
  FiniteIntervals.of_fin 839800 200 complete_chunk4199

#print axioms interval_chunk4190
end Erdos184Work.PureFiveFilter4
