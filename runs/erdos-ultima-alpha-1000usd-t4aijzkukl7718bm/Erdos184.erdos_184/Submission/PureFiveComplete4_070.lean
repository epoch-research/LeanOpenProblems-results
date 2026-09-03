import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk700 : ∀ i : Fin 200, Compatible (140000 + i.val) →
    (table.lookup (140000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk700 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 140000 140200 :=
  FiniteIntervals.of_fin 140000 200 complete_chunk700

lemma complete_chunk701 : ∀ i : Fin 200, Compatible (140200 + i.val) →
    (table.lookup (140200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk701 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 140200 140400 :=
  FiniteIntervals.of_fin 140200 200 complete_chunk701

lemma complete_chunk702 : ∀ i : Fin 200, Compatible (140400 + i.val) →
    (table.lookup (140400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk702 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 140400 140600 :=
  FiniteIntervals.of_fin 140400 200 complete_chunk702

lemma complete_chunk703 : ∀ i : Fin 200, Compatible (140600 + i.val) →
    (table.lookup (140600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk703 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 140600 140800 :=
  FiniteIntervals.of_fin 140600 200 complete_chunk703

lemma complete_chunk704 : ∀ i : Fin 200, Compatible (140800 + i.val) →
    (table.lookup (140800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk704 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 140800 141000 :=
  FiniteIntervals.of_fin 140800 200 complete_chunk704

lemma complete_chunk705 : ∀ i : Fin 200, Compatible (141000 + i.val) →
    (table.lookup (141000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk705 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 141000 141200 :=
  FiniteIntervals.of_fin 141000 200 complete_chunk705

lemma complete_chunk706 : ∀ i : Fin 200, Compatible (141200 + i.val) →
    (table.lookup (141200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk706 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 141200 141400 :=
  FiniteIntervals.of_fin 141200 200 complete_chunk706

lemma complete_chunk707 : ∀ i : Fin 200, Compatible (141400 + i.val) →
    (table.lookup (141400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk707 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 141400 141600 :=
  FiniteIntervals.of_fin 141400 200 complete_chunk707

lemma complete_chunk708 : ∀ i : Fin 200, Compatible (141600 + i.val) →
    (table.lookup (141600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk708 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 141600 141800 :=
  FiniteIntervals.of_fin 141600 200 complete_chunk708

lemma complete_chunk709 : ∀ i : Fin 200, Compatible (141800 + i.val) →
    (table.lookup (141800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk709 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 141800 142000 :=
  FiniteIntervals.of_fin 141800 200 complete_chunk709

#print axioms interval_chunk700
end Erdos184Work.PureFiveFilter4
