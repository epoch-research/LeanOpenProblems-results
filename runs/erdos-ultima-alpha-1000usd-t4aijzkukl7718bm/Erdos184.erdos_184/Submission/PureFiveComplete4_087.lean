import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk870 : ∀ i : Fin 200, Compatible (174000 + i.val) →
    (table.lookup (174000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk870 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 174000 174200 :=
  FiniteIntervals.of_fin 174000 200 complete_chunk870

lemma complete_chunk871 : ∀ i : Fin 200, Compatible (174200 + i.val) →
    (table.lookup (174200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk871 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 174200 174400 :=
  FiniteIntervals.of_fin 174200 200 complete_chunk871

lemma complete_chunk872 : ∀ i : Fin 200, Compatible (174400 + i.val) →
    (table.lookup (174400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk872 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 174400 174600 :=
  FiniteIntervals.of_fin 174400 200 complete_chunk872

lemma complete_chunk873 : ∀ i : Fin 200, Compatible (174600 + i.val) →
    (table.lookup (174600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk873 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 174600 174800 :=
  FiniteIntervals.of_fin 174600 200 complete_chunk873

lemma complete_chunk874 : ∀ i : Fin 200, Compatible (174800 + i.val) →
    (table.lookup (174800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk874 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 174800 175000 :=
  FiniteIntervals.of_fin 174800 200 complete_chunk874

lemma complete_chunk875 : ∀ i : Fin 200, Compatible (175000 + i.val) →
    (table.lookup (175000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk875 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 175000 175200 :=
  FiniteIntervals.of_fin 175000 200 complete_chunk875

lemma complete_chunk876 : ∀ i : Fin 200, Compatible (175200 + i.val) →
    (table.lookup (175200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk876 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 175200 175400 :=
  FiniteIntervals.of_fin 175200 200 complete_chunk876

lemma complete_chunk877 : ∀ i : Fin 200, Compatible (175400 + i.val) →
    (table.lookup (175400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk877 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 175400 175600 :=
  FiniteIntervals.of_fin 175400 200 complete_chunk877

lemma complete_chunk878 : ∀ i : Fin 200, Compatible (175600 + i.val) →
    (table.lookup (175600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk878 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 175600 175800 :=
  FiniteIntervals.of_fin 175600 200 complete_chunk878

lemma complete_chunk879 : ∀ i : Fin 200, Compatible (175800 + i.val) →
    (table.lookup (175800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk879 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 175800 176000 :=
  FiniteIntervals.of_fin 175800 200 complete_chunk879

#print axioms interval_chunk870
end Erdos184Work.PureFiveFilter4
