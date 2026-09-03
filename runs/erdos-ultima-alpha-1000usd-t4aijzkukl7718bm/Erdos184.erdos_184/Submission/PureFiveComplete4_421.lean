import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4210 : ∀ i : Fin 200, Compatible (842000 + i.val) →
    (table.lookup (842000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4210 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 842000 842200 :=
  FiniteIntervals.of_fin 842000 200 complete_chunk4210

lemma complete_chunk4211 : ∀ i : Fin 200, Compatible (842200 + i.val) →
    (table.lookup (842200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4211 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 842200 842400 :=
  FiniteIntervals.of_fin 842200 200 complete_chunk4211

lemma complete_chunk4212 : ∀ i : Fin 200, Compatible (842400 + i.val) →
    (table.lookup (842400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4212 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 842400 842600 :=
  FiniteIntervals.of_fin 842400 200 complete_chunk4212

lemma complete_chunk4213 : ∀ i : Fin 200, Compatible (842600 + i.val) →
    (table.lookup (842600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4213 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 842600 842800 :=
  FiniteIntervals.of_fin 842600 200 complete_chunk4213

lemma complete_chunk4214 : ∀ i : Fin 200, Compatible (842800 + i.val) →
    (table.lookup (842800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4214 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 842800 843000 :=
  FiniteIntervals.of_fin 842800 200 complete_chunk4214

lemma complete_chunk4215 : ∀ i : Fin 200, Compatible (843000 + i.val) →
    (table.lookup (843000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4215 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 843000 843200 :=
  FiniteIntervals.of_fin 843000 200 complete_chunk4215

lemma complete_chunk4216 : ∀ i : Fin 200, Compatible (843200 + i.val) →
    (table.lookup (843200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4216 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 843200 843400 :=
  FiniteIntervals.of_fin 843200 200 complete_chunk4216

lemma complete_chunk4217 : ∀ i : Fin 200, Compatible (843400 + i.val) →
    (table.lookup (843400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4217 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 843400 843600 :=
  FiniteIntervals.of_fin 843400 200 complete_chunk4217

lemma complete_chunk4218 : ∀ i : Fin 200, Compatible (843600 + i.val) →
    (table.lookup (843600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4218 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 843600 843800 :=
  FiniteIntervals.of_fin 843600 200 complete_chunk4218

lemma complete_chunk4219 : ∀ i : Fin 200, Compatible (843800 + i.val) →
    (table.lookup (843800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4219 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 843800 844000 :=
  FiniteIntervals.of_fin 843800 200 complete_chunk4219

#print axioms interval_chunk4210
end Erdos184Work.PureFiveFilter4
