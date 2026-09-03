import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3120 : ∀ i : Fin 200, Compatible (624000 + i.val) →
    (table.lookup (624000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3120 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 624000 624200 :=
  FiniteIntervals.of_fin 624000 200 complete_chunk3120

lemma complete_chunk3121 : ∀ i : Fin 200, Compatible (624200 + i.val) →
    (table.lookup (624200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3121 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 624200 624400 :=
  FiniteIntervals.of_fin 624200 200 complete_chunk3121

lemma complete_chunk3122 : ∀ i : Fin 200, Compatible (624400 + i.val) →
    (table.lookup (624400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3122 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 624400 624600 :=
  FiniteIntervals.of_fin 624400 200 complete_chunk3122

lemma complete_chunk3123 : ∀ i : Fin 200, Compatible (624600 + i.val) →
    (table.lookup (624600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3123 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 624600 624800 :=
  FiniteIntervals.of_fin 624600 200 complete_chunk3123

lemma complete_chunk3124 : ∀ i : Fin 200, Compatible (624800 + i.val) →
    (table.lookup (624800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3124 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 624800 625000 :=
  FiniteIntervals.of_fin 624800 200 complete_chunk3124

lemma complete_chunk3125 : ∀ i : Fin 200, Compatible (625000 + i.val) →
    (table.lookup (625000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3125 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 625000 625200 :=
  FiniteIntervals.of_fin 625000 200 complete_chunk3125

lemma complete_chunk3126 : ∀ i : Fin 200, Compatible (625200 + i.val) →
    (table.lookup (625200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3126 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 625200 625400 :=
  FiniteIntervals.of_fin 625200 200 complete_chunk3126

lemma complete_chunk3127 : ∀ i : Fin 200, Compatible (625400 + i.val) →
    (table.lookup (625400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3127 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 625400 625600 :=
  FiniteIntervals.of_fin 625400 200 complete_chunk3127

lemma complete_chunk3128 : ∀ i : Fin 200, Compatible (625600 + i.val) →
    (table.lookup (625600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3128 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 625600 625800 :=
  FiniteIntervals.of_fin 625600 200 complete_chunk3128

lemma complete_chunk3129 : ∀ i : Fin 200, Compatible (625800 + i.val) →
    (table.lookup (625800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3129 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 625800 626000 :=
  FiniteIntervals.of_fin 625800 200 complete_chunk3129

#print axioms interval_chunk3120
end Erdos184Work.PureFiveFilter4
