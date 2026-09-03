import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3160 : ∀ i : Fin 200, Compatible (632000 + i.val) →
    (table.lookup (632000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 632000 632200 :=
  FiniteIntervals.of_fin 632000 200 complete_chunk3160

lemma complete_chunk3161 : ∀ i : Fin 200, Compatible (632200 + i.val) →
    (table.lookup (632200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 632200 632400 :=
  FiniteIntervals.of_fin 632200 200 complete_chunk3161

lemma complete_chunk3162 : ∀ i : Fin 200, Compatible (632400 + i.val) →
    (table.lookup (632400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 632400 632600 :=
  FiniteIntervals.of_fin 632400 200 complete_chunk3162

lemma complete_chunk3163 : ∀ i : Fin 200, Compatible (632600 + i.val) →
    (table.lookup (632600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 632600 632800 :=
  FiniteIntervals.of_fin 632600 200 complete_chunk3163

lemma complete_chunk3164 : ∀ i : Fin 200, Compatible (632800 + i.val) →
    (table.lookup (632800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 632800 633000 :=
  FiniteIntervals.of_fin 632800 200 complete_chunk3164

lemma complete_chunk3165 : ∀ i : Fin 200, Compatible (633000 + i.val) →
    (table.lookup (633000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 633000 633200 :=
  FiniteIntervals.of_fin 633000 200 complete_chunk3165

lemma complete_chunk3166 : ∀ i : Fin 200, Compatible (633200 + i.val) →
    (table.lookup (633200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 633200 633400 :=
  FiniteIntervals.of_fin 633200 200 complete_chunk3166

lemma complete_chunk3167 : ∀ i : Fin 200, Compatible (633400 + i.val) →
    (table.lookup (633400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 633400 633600 :=
  FiniteIntervals.of_fin 633400 200 complete_chunk3167

lemma complete_chunk3168 : ∀ i : Fin 200, Compatible (633600 + i.val) →
    (table.lookup (633600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 633600 633800 :=
  FiniteIntervals.of_fin 633600 200 complete_chunk3168

lemma complete_chunk3169 : ∀ i : Fin 200, Compatible (633800 + i.val) →
    (table.lookup (633800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 633800 634000 :=
  FiniteIntervals.of_fin 633800 200 complete_chunk3169

#print axioms interval_chunk3160
end Erdos184Work.PureFiveFilter4
