import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5190 : ∀ i : Fin 200, Compatible (1038000 + i.val) →
    (table.lookup (1038000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5190 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1038000 1038200 :=
  FiniteIntervals.of_fin 1038000 200 complete_chunk5190

lemma complete_chunk5191 : ∀ i : Fin 200, Compatible (1038200 + i.val) →
    (table.lookup (1038200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5191 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1038200 1038400 :=
  FiniteIntervals.of_fin 1038200 200 complete_chunk5191

lemma complete_chunk5192 : ∀ i : Fin 200, Compatible (1038400 + i.val) →
    (table.lookup (1038400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5192 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1038400 1038600 :=
  FiniteIntervals.of_fin 1038400 200 complete_chunk5192

lemma complete_chunk5193 : ∀ i : Fin 200, Compatible (1038600 + i.val) →
    (table.lookup (1038600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5193 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1038600 1038800 :=
  FiniteIntervals.of_fin 1038600 200 complete_chunk5193

lemma complete_chunk5194 : ∀ i : Fin 200, Compatible (1038800 + i.val) →
    (table.lookup (1038800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5194 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1038800 1039000 :=
  FiniteIntervals.of_fin 1038800 200 complete_chunk5194

lemma complete_chunk5195 : ∀ i : Fin 200, Compatible (1039000 + i.val) →
    (table.lookup (1039000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5195 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1039000 1039200 :=
  FiniteIntervals.of_fin 1039000 200 complete_chunk5195

lemma complete_chunk5196 : ∀ i : Fin 200, Compatible (1039200 + i.val) →
    (table.lookup (1039200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5196 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1039200 1039400 :=
  FiniteIntervals.of_fin 1039200 200 complete_chunk5196

lemma complete_chunk5197 : ∀ i : Fin 200, Compatible (1039400 + i.val) →
    (table.lookup (1039400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5197 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1039400 1039600 :=
  FiniteIntervals.of_fin 1039400 200 complete_chunk5197

lemma complete_chunk5198 : ∀ i : Fin 200, Compatible (1039600 + i.val) →
    (table.lookup (1039600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5198 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1039600 1039800 :=
  FiniteIntervals.of_fin 1039600 200 complete_chunk5198

lemma complete_chunk5199 : ∀ i : Fin 200, Compatible (1039800 + i.val) →
    (table.lookup (1039800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5199 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1039800 1040000 :=
  FiniteIntervals.of_fin 1039800 200 complete_chunk5199

#print axioms interval_chunk5190
end Erdos184Work.PureFiveFilter4
