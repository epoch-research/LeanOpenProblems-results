import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2870 : ∀ i : Fin 200, Compatible (574000 + i.val) →
    (table.lookup (574000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2870 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 574000 574200 :=
  FiniteIntervals.of_fin 574000 200 complete_chunk2870

lemma complete_chunk2871 : ∀ i : Fin 200, Compatible (574200 + i.val) →
    (table.lookup (574200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2871 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 574200 574400 :=
  FiniteIntervals.of_fin 574200 200 complete_chunk2871

lemma complete_chunk2872 : ∀ i : Fin 200, Compatible (574400 + i.val) →
    (table.lookup (574400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2872 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 574400 574600 :=
  FiniteIntervals.of_fin 574400 200 complete_chunk2872

lemma complete_chunk2873 : ∀ i : Fin 200, Compatible (574600 + i.val) →
    (table.lookup (574600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2873 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 574600 574800 :=
  FiniteIntervals.of_fin 574600 200 complete_chunk2873

lemma complete_chunk2874 : ∀ i : Fin 200, Compatible (574800 + i.val) →
    (table.lookup (574800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2874 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 574800 575000 :=
  FiniteIntervals.of_fin 574800 200 complete_chunk2874

lemma complete_chunk2875 : ∀ i : Fin 200, Compatible (575000 + i.val) →
    (table.lookup (575000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2875 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 575000 575200 :=
  FiniteIntervals.of_fin 575000 200 complete_chunk2875

lemma complete_chunk2876 : ∀ i : Fin 200, Compatible (575200 + i.val) →
    (table.lookup (575200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2876 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 575200 575400 :=
  FiniteIntervals.of_fin 575200 200 complete_chunk2876

lemma complete_chunk2877 : ∀ i : Fin 200, Compatible (575400 + i.val) →
    (table.lookup (575400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2877 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 575400 575600 :=
  FiniteIntervals.of_fin 575400 200 complete_chunk2877

lemma complete_chunk2878 : ∀ i : Fin 200, Compatible (575600 + i.val) →
    (table.lookup (575600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2878 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 575600 575800 :=
  FiniteIntervals.of_fin 575600 200 complete_chunk2878

lemma complete_chunk2879 : ∀ i : Fin 200, Compatible (575800 + i.val) →
    (table.lookup (575800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2879 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 575800 576000 :=
  FiniteIntervals.of_fin 575800 200 complete_chunk2879

#print axioms interval_chunk2870
end Erdos184Work.PureFiveFilter4
