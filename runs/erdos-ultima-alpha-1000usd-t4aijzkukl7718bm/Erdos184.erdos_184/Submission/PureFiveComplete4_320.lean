import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3200 : ∀ i : Fin 200, Compatible (640000 + i.val) →
    (table.lookup (640000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 640000 640200 :=
  FiniteIntervals.of_fin 640000 200 complete_chunk3200

lemma complete_chunk3201 : ∀ i : Fin 200, Compatible (640200 + i.val) →
    (table.lookup (640200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 640200 640400 :=
  FiniteIntervals.of_fin 640200 200 complete_chunk3201

lemma complete_chunk3202 : ∀ i : Fin 200, Compatible (640400 + i.val) →
    (table.lookup (640400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 640400 640600 :=
  FiniteIntervals.of_fin 640400 200 complete_chunk3202

lemma complete_chunk3203 : ∀ i : Fin 200, Compatible (640600 + i.val) →
    (table.lookup (640600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 640600 640800 :=
  FiniteIntervals.of_fin 640600 200 complete_chunk3203

lemma complete_chunk3204 : ∀ i : Fin 200, Compatible (640800 + i.val) →
    (table.lookup (640800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 640800 641000 :=
  FiniteIntervals.of_fin 640800 200 complete_chunk3204

lemma complete_chunk3205 : ∀ i : Fin 200, Compatible (641000 + i.val) →
    (table.lookup (641000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 641000 641200 :=
  FiniteIntervals.of_fin 641000 200 complete_chunk3205

lemma complete_chunk3206 : ∀ i : Fin 200, Compatible (641200 + i.val) →
    (table.lookup (641200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 641200 641400 :=
  FiniteIntervals.of_fin 641200 200 complete_chunk3206

lemma complete_chunk3207 : ∀ i : Fin 200, Compatible (641400 + i.val) →
    (table.lookup (641400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 641400 641600 :=
  FiniteIntervals.of_fin 641400 200 complete_chunk3207

lemma complete_chunk3208 : ∀ i : Fin 200, Compatible (641600 + i.val) →
    (table.lookup (641600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 641600 641800 :=
  FiniteIntervals.of_fin 641600 200 complete_chunk3208

lemma complete_chunk3209 : ∀ i : Fin 200, Compatible (641800 + i.val) →
    (table.lookup (641800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 641800 642000 :=
  FiniteIntervals.of_fin 641800 200 complete_chunk3209

#print axioms interval_chunk3200
end Erdos184Work.PureFiveFilter4
