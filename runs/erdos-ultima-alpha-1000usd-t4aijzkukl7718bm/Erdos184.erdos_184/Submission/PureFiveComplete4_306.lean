import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk3060 : ∀ i : Fin 200, Compatible (612000 + i.val) →
    (table.lookup (612000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3060 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 612000 612200 :=
  FiniteIntervals.of_fin 612000 200 complete_chunk3060

lemma complete_chunk3061 : ∀ i : Fin 200, Compatible (612200 + i.val) →
    (table.lookup (612200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3061 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 612200 612400 :=
  FiniteIntervals.of_fin 612200 200 complete_chunk3061

lemma complete_chunk3062 : ∀ i : Fin 200, Compatible (612400 + i.val) →
    (table.lookup (612400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3062 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 612400 612600 :=
  FiniteIntervals.of_fin 612400 200 complete_chunk3062

lemma complete_chunk3063 : ∀ i : Fin 200, Compatible (612600 + i.val) →
    (table.lookup (612600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3063 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 612600 612800 :=
  FiniteIntervals.of_fin 612600 200 complete_chunk3063

lemma complete_chunk3064 : ∀ i : Fin 200, Compatible (612800 + i.val) →
    (table.lookup (612800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3064 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 612800 613000 :=
  FiniteIntervals.of_fin 612800 200 complete_chunk3064

lemma complete_chunk3065 : ∀ i : Fin 200, Compatible (613000 + i.val) →
    (table.lookup (613000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3065 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 613000 613200 :=
  FiniteIntervals.of_fin 613000 200 complete_chunk3065

lemma complete_chunk3066 : ∀ i : Fin 200, Compatible (613200 + i.val) →
    (table.lookup (613200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3066 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 613200 613400 :=
  FiniteIntervals.of_fin 613200 200 complete_chunk3066

lemma complete_chunk3067 : ∀ i : Fin 200, Compatible (613400 + i.val) →
    (table.lookup (613400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3067 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 613400 613600 :=
  FiniteIntervals.of_fin 613400 200 complete_chunk3067

lemma complete_chunk3068 : ∀ i : Fin 200, Compatible (613600 + i.val) →
    (table.lookup (613600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3068 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 613600 613800 :=
  FiniteIntervals.of_fin 613600 200 complete_chunk3068

lemma complete_chunk3069 : ∀ i : Fin 200, Compatible (613800 + i.val) →
    (table.lookup (613800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk3069 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 613800 614000 :=
  FiniteIntervals.of_fin 613800 200 complete_chunk3069

#print axioms interval_chunk3060
end Erdos184Work.PureFiveFilter4
