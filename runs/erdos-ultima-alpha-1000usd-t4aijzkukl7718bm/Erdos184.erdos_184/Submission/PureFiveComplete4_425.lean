import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4250 : ∀ i : Fin 200, Compatible (850000 + i.val) →
    (table.lookup (850000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4250 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 850000 850200 :=
  FiniteIntervals.of_fin 850000 200 complete_chunk4250

lemma complete_chunk4251 : ∀ i : Fin 200, Compatible (850200 + i.val) →
    (table.lookup (850200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4251 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 850200 850400 :=
  FiniteIntervals.of_fin 850200 200 complete_chunk4251

lemma complete_chunk4252 : ∀ i : Fin 200, Compatible (850400 + i.val) →
    (table.lookup (850400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4252 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 850400 850600 :=
  FiniteIntervals.of_fin 850400 200 complete_chunk4252

lemma complete_chunk4253 : ∀ i : Fin 200, Compatible (850600 + i.val) →
    (table.lookup (850600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4253 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 850600 850800 :=
  FiniteIntervals.of_fin 850600 200 complete_chunk4253

lemma complete_chunk4254 : ∀ i : Fin 200, Compatible (850800 + i.val) →
    (table.lookup (850800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4254 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 850800 851000 :=
  FiniteIntervals.of_fin 850800 200 complete_chunk4254

lemma complete_chunk4255 : ∀ i : Fin 200, Compatible (851000 + i.val) →
    (table.lookup (851000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4255 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 851000 851200 :=
  FiniteIntervals.of_fin 851000 200 complete_chunk4255

lemma complete_chunk4256 : ∀ i : Fin 200, Compatible (851200 + i.val) →
    (table.lookup (851200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4256 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 851200 851400 :=
  FiniteIntervals.of_fin 851200 200 complete_chunk4256

lemma complete_chunk4257 : ∀ i : Fin 200, Compatible (851400 + i.val) →
    (table.lookup (851400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4257 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 851400 851600 :=
  FiniteIntervals.of_fin 851400 200 complete_chunk4257

lemma complete_chunk4258 : ∀ i : Fin 200, Compatible (851600 + i.val) →
    (table.lookup (851600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4258 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 851600 851800 :=
  FiniteIntervals.of_fin 851600 200 complete_chunk4258

lemma complete_chunk4259 : ∀ i : Fin 200, Compatible (851800 + i.val) →
    (table.lookup (851800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4259 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 851800 852000 :=
  FiniteIntervals.of_fin 851800 200 complete_chunk4259

#print axioms interval_chunk4250
end Erdos184Work.PureFiveFilter4
