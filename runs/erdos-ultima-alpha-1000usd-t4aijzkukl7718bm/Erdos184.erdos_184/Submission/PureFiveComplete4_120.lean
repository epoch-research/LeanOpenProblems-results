import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1200 : ∀ i : Fin 200, Compatible (240000 + i.val) →
    (table.lookup (240000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1200 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 240000 240200 :=
  FiniteIntervals.of_fin 240000 200 complete_chunk1200

lemma complete_chunk1201 : ∀ i : Fin 200, Compatible (240200 + i.val) →
    (table.lookup (240200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1201 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 240200 240400 :=
  FiniteIntervals.of_fin 240200 200 complete_chunk1201

lemma complete_chunk1202 : ∀ i : Fin 200, Compatible (240400 + i.val) →
    (table.lookup (240400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1202 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 240400 240600 :=
  FiniteIntervals.of_fin 240400 200 complete_chunk1202

lemma complete_chunk1203 : ∀ i : Fin 200, Compatible (240600 + i.val) →
    (table.lookup (240600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1203 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 240600 240800 :=
  FiniteIntervals.of_fin 240600 200 complete_chunk1203

lemma complete_chunk1204 : ∀ i : Fin 200, Compatible (240800 + i.val) →
    (table.lookup (240800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1204 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 240800 241000 :=
  FiniteIntervals.of_fin 240800 200 complete_chunk1204

lemma complete_chunk1205 : ∀ i : Fin 200, Compatible (241000 + i.val) →
    (table.lookup (241000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1205 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 241000 241200 :=
  FiniteIntervals.of_fin 241000 200 complete_chunk1205

lemma complete_chunk1206 : ∀ i : Fin 200, Compatible (241200 + i.val) →
    (table.lookup (241200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1206 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 241200 241400 :=
  FiniteIntervals.of_fin 241200 200 complete_chunk1206

lemma complete_chunk1207 : ∀ i : Fin 200, Compatible (241400 + i.val) →
    (table.lookup (241400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1207 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 241400 241600 :=
  FiniteIntervals.of_fin 241400 200 complete_chunk1207

lemma complete_chunk1208 : ∀ i : Fin 200, Compatible (241600 + i.val) →
    (table.lookup (241600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1208 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 241600 241800 :=
  FiniteIntervals.of_fin 241600 200 complete_chunk1208

lemma complete_chunk1209 : ∀ i : Fin 200, Compatible (241800 + i.val) →
    (table.lookup (241800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1209 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 241800 242000 :=
  FiniteIntervals.of_fin 241800 200 complete_chunk1209

#print axioms interval_chunk1200
end Erdos184Work.PureFiveFilter4
