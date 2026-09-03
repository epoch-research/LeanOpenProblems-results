import Submission.PureFiveFilter3
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter3
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk200 : ∀ i : Fin 200, Compatible (40000 + i.val) →
    (table.lookup (40000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 40000 40200 :=
  FiniteIntervals.of_fin 40000 200 complete_chunk200

lemma complete_chunk201 : ∀ i : Fin 200, Compatible (40200 + i.val) →
    (table.lookup (40200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 40200 40400 :=
  FiniteIntervals.of_fin 40200 200 complete_chunk201

lemma complete_chunk202 : ∀ i : Fin 200, Compatible (40400 + i.val) →
    (table.lookup (40400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 40400 40600 :=
  FiniteIntervals.of_fin 40400 200 complete_chunk202

lemma complete_chunk203 : ∀ i : Fin 200, Compatible (40600 + i.val) →
    (table.lookup (40600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 40600 40800 :=
  FiniteIntervals.of_fin 40600 200 complete_chunk203

lemma complete_chunk204 : ∀ i : Fin 200, Compatible (40800 + i.val) →
    (table.lookup (40800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 40800 41000 :=
  FiniteIntervals.of_fin 40800 200 complete_chunk204

lemma complete_chunk205 : ∀ i : Fin 200, Compatible (41000 + i.val) →
    (table.lookup (41000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 41000 41200 :=
  FiniteIntervals.of_fin 41000 200 complete_chunk205

lemma complete_chunk206 : ∀ i : Fin 200, Compatible (41200 + i.val) →
    (table.lookup (41200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 41200 41400 :=
  FiniteIntervals.of_fin 41200 200 complete_chunk206

lemma complete_chunk207 : ∀ i : Fin 200, Compatible (41400 + i.val) →
    (table.lookup (41400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 41400 41600 :=
  FiniteIntervals.of_fin 41400 200 complete_chunk207

lemma complete_chunk208 : ∀ i : Fin 200, Compatible (41600 + i.val) →
    (table.lookup (41600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 41600 41800 :=
  FiniteIntervals.of_fin 41600 200 complete_chunk208

lemma complete_chunk209 : ∀ i : Fin 200, Compatible (41800 + i.val) →
    (table.lookup (41800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 41800 42000 :=
  FiniteIntervals.of_fin 41800 200 complete_chunk209

#print axioms interval_chunk200
end Erdos184Work.PureFiveFilter3
