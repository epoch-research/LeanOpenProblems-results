import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5700 : ∀ i : Fin 200, Compatible (1140000 + i.val) →
    (table.lookup (1140000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5700 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1140000 1140200 :=
  FiniteIntervals.of_fin 1140000 200 complete_chunk5700

lemma complete_chunk5701 : ∀ i : Fin 200, Compatible (1140200 + i.val) →
    (table.lookup (1140200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5701 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1140200 1140400 :=
  FiniteIntervals.of_fin 1140200 200 complete_chunk5701

lemma complete_chunk5702 : ∀ i : Fin 200, Compatible (1140400 + i.val) →
    (table.lookup (1140400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5702 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1140400 1140600 :=
  FiniteIntervals.of_fin 1140400 200 complete_chunk5702

lemma complete_chunk5703 : ∀ i : Fin 200, Compatible (1140600 + i.val) →
    (table.lookup (1140600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5703 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1140600 1140800 :=
  FiniteIntervals.of_fin 1140600 200 complete_chunk5703

lemma complete_chunk5704 : ∀ i : Fin 200, Compatible (1140800 + i.val) →
    (table.lookup (1140800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5704 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1140800 1141000 :=
  FiniteIntervals.of_fin 1140800 200 complete_chunk5704

lemma complete_chunk5705 : ∀ i : Fin 200, Compatible (1141000 + i.val) →
    (table.lookup (1141000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5705 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1141000 1141200 :=
  FiniteIntervals.of_fin 1141000 200 complete_chunk5705

lemma complete_chunk5706 : ∀ i : Fin 200, Compatible (1141200 + i.val) →
    (table.lookup (1141200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5706 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1141200 1141400 :=
  FiniteIntervals.of_fin 1141200 200 complete_chunk5706

lemma complete_chunk5707 : ∀ i : Fin 200, Compatible (1141400 + i.val) →
    (table.lookup (1141400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5707 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1141400 1141600 :=
  FiniteIntervals.of_fin 1141400 200 complete_chunk5707

lemma complete_chunk5708 : ∀ i : Fin 200, Compatible (1141600 + i.val) →
    (table.lookup (1141600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5708 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1141600 1141800 :=
  FiniteIntervals.of_fin 1141600 200 complete_chunk5708

lemma complete_chunk5709 : ∀ i : Fin 200, Compatible (1141800 + i.val) →
    (table.lookup (1141800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5709 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1141800 1142000 :=
  FiniteIntervals.of_fin 1141800 200 complete_chunk5709

#print axioms interval_chunk5700
end Erdos184Work.PureFiveFilter4
