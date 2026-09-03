import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5870 : ∀ i : Fin 200, Compatible (1174000 + i.val) →
    (table.lookup (1174000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5870 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1174000 1174200 :=
  FiniteIntervals.of_fin 1174000 200 complete_chunk5870

lemma complete_chunk5871 : ∀ i : Fin 200, Compatible (1174200 + i.val) →
    (table.lookup (1174200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5871 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1174200 1174400 :=
  FiniteIntervals.of_fin 1174200 200 complete_chunk5871

lemma complete_chunk5872 : ∀ i : Fin 200, Compatible (1174400 + i.val) →
    (table.lookup (1174400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5872 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1174400 1174600 :=
  FiniteIntervals.of_fin 1174400 200 complete_chunk5872

lemma complete_chunk5873 : ∀ i : Fin 200, Compatible (1174600 + i.val) →
    (table.lookup (1174600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5873 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1174600 1174800 :=
  FiniteIntervals.of_fin 1174600 200 complete_chunk5873

lemma complete_chunk5874 : ∀ i : Fin 200, Compatible (1174800 + i.val) →
    (table.lookup (1174800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5874 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1174800 1175000 :=
  FiniteIntervals.of_fin 1174800 200 complete_chunk5874

lemma complete_chunk5875 : ∀ i : Fin 200, Compatible (1175000 + i.val) →
    (table.lookup (1175000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5875 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1175000 1175200 :=
  FiniteIntervals.of_fin 1175000 200 complete_chunk5875

lemma complete_chunk5876 : ∀ i : Fin 200, Compatible (1175200 + i.val) →
    (table.lookup (1175200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5876 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1175200 1175400 :=
  FiniteIntervals.of_fin 1175200 200 complete_chunk5876

lemma complete_chunk5877 : ∀ i : Fin 200, Compatible (1175400 + i.val) →
    (table.lookup (1175400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5877 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1175400 1175600 :=
  FiniteIntervals.of_fin 1175400 200 complete_chunk5877

lemma complete_chunk5878 : ∀ i : Fin 200, Compatible (1175600 + i.val) →
    (table.lookup (1175600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5878 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1175600 1175800 :=
  FiniteIntervals.of_fin 1175600 200 complete_chunk5878

lemma complete_chunk5879 : ∀ i : Fin 200, Compatible (1175800 + i.val) →
    (table.lookup (1175800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5879 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1175800 1176000 :=
  FiniteIntervals.of_fin 1175800 200 complete_chunk5879

#print axioms interval_chunk5870
end Erdos184Work.PureFiveFilter4
