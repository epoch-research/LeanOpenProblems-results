import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4600 : ∀ i : Fin 200, Compatible (920000 + i.val) →
    (table.lookup (920000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4600 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 920000 920200 :=
  FiniteIntervals.of_fin 920000 200 complete_chunk4600

lemma complete_chunk4601 : ∀ i : Fin 200, Compatible (920200 + i.val) →
    (table.lookup (920200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4601 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 920200 920400 :=
  FiniteIntervals.of_fin 920200 200 complete_chunk4601

lemma complete_chunk4602 : ∀ i : Fin 200, Compatible (920400 + i.val) →
    (table.lookup (920400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4602 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 920400 920600 :=
  FiniteIntervals.of_fin 920400 200 complete_chunk4602

lemma complete_chunk4603 : ∀ i : Fin 200, Compatible (920600 + i.val) →
    (table.lookup (920600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4603 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 920600 920800 :=
  FiniteIntervals.of_fin 920600 200 complete_chunk4603

lemma complete_chunk4604 : ∀ i : Fin 200, Compatible (920800 + i.val) →
    (table.lookup (920800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4604 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 920800 921000 :=
  FiniteIntervals.of_fin 920800 200 complete_chunk4604

lemma complete_chunk4605 : ∀ i : Fin 200, Compatible (921000 + i.val) →
    (table.lookup (921000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4605 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 921000 921200 :=
  FiniteIntervals.of_fin 921000 200 complete_chunk4605

lemma complete_chunk4606 : ∀ i : Fin 200, Compatible (921200 + i.val) →
    (table.lookup (921200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4606 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 921200 921400 :=
  FiniteIntervals.of_fin 921200 200 complete_chunk4606

lemma complete_chunk4607 : ∀ i : Fin 200, Compatible (921400 + i.val) →
    (table.lookup (921400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4607 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 921400 921600 :=
  FiniteIntervals.of_fin 921400 200 complete_chunk4607

lemma complete_chunk4608 : ∀ i : Fin 200, Compatible (921600 + i.val) →
    (table.lookup (921600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4608 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 921600 921800 :=
  FiniteIntervals.of_fin 921600 200 complete_chunk4608

lemma complete_chunk4609 : ∀ i : Fin 200, Compatible (921800 + i.val) →
    (table.lookup (921800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4609 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 921800 922000 :=
  FiniteIntervals.of_fin 921800 200 complete_chunk4609

#print axioms interval_chunk4600
end Erdos184Work.PureFiveFilter4
