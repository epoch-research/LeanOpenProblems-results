import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5600 : ∀ i : Fin 200, Compatible (1120000 + i.val) →
    (table.lookup (1120000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5600 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1120000 1120200 :=
  FiniteIntervals.of_fin 1120000 200 complete_chunk5600

lemma complete_chunk5601 : ∀ i : Fin 200, Compatible (1120200 + i.val) →
    (table.lookup (1120200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5601 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1120200 1120400 :=
  FiniteIntervals.of_fin 1120200 200 complete_chunk5601

lemma complete_chunk5602 : ∀ i : Fin 200, Compatible (1120400 + i.val) →
    (table.lookup (1120400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5602 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1120400 1120600 :=
  FiniteIntervals.of_fin 1120400 200 complete_chunk5602

lemma complete_chunk5603 : ∀ i : Fin 200, Compatible (1120600 + i.val) →
    (table.lookup (1120600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5603 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1120600 1120800 :=
  FiniteIntervals.of_fin 1120600 200 complete_chunk5603

lemma complete_chunk5604 : ∀ i : Fin 200, Compatible (1120800 + i.val) →
    (table.lookup (1120800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5604 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1120800 1121000 :=
  FiniteIntervals.of_fin 1120800 200 complete_chunk5604

lemma complete_chunk5605 : ∀ i : Fin 200, Compatible (1121000 + i.val) →
    (table.lookup (1121000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5605 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1121000 1121200 :=
  FiniteIntervals.of_fin 1121000 200 complete_chunk5605

lemma complete_chunk5606 : ∀ i : Fin 200, Compatible (1121200 + i.val) →
    (table.lookup (1121200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5606 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1121200 1121400 :=
  FiniteIntervals.of_fin 1121200 200 complete_chunk5606

lemma complete_chunk5607 : ∀ i : Fin 200, Compatible (1121400 + i.val) →
    (table.lookup (1121400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5607 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1121400 1121600 :=
  FiniteIntervals.of_fin 1121400 200 complete_chunk5607

lemma complete_chunk5608 : ∀ i : Fin 200, Compatible (1121600 + i.val) →
    (table.lookup (1121600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5608 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1121600 1121800 :=
  FiniteIntervals.of_fin 1121600 200 complete_chunk5608

lemma complete_chunk5609 : ∀ i : Fin 200, Compatible (1121800 + i.val) →
    (table.lookup (1121800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5609 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1121800 1122000 :=
  FiniteIntervals.of_fin 1121800 200 complete_chunk5609

#print axioms interval_chunk5600
end Erdos184Work.PureFiveFilter4
