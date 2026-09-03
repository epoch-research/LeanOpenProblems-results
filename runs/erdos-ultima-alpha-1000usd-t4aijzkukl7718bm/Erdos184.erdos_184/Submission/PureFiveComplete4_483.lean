import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4830 : ∀ i : Fin 200, Compatible (966000 + i.val) →
    (table.lookup (966000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4830 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 966000 966200 :=
  FiniteIntervals.of_fin 966000 200 complete_chunk4830

lemma complete_chunk4831 : ∀ i : Fin 200, Compatible (966200 + i.val) →
    (table.lookup (966200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4831 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 966200 966400 :=
  FiniteIntervals.of_fin 966200 200 complete_chunk4831

lemma complete_chunk4832 : ∀ i : Fin 200, Compatible (966400 + i.val) →
    (table.lookup (966400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4832 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 966400 966600 :=
  FiniteIntervals.of_fin 966400 200 complete_chunk4832

lemma complete_chunk4833 : ∀ i : Fin 200, Compatible (966600 + i.val) →
    (table.lookup (966600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4833 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 966600 966800 :=
  FiniteIntervals.of_fin 966600 200 complete_chunk4833

lemma complete_chunk4834 : ∀ i : Fin 200, Compatible (966800 + i.val) →
    (table.lookup (966800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4834 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 966800 967000 :=
  FiniteIntervals.of_fin 966800 200 complete_chunk4834

lemma complete_chunk4835 : ∀ i : Fin 200, Compatible (967000 + i.val) →
    (table.lookup (967000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4835 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 967000 967200 :=
  FiniteIntervals.of_fin 967000 200 complete_chunk4835

lemma complete_chunk4836 : ∀ i : Fin 200, Compatible (967200 + i.val) →
    (table.lookup (967200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4836 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 967200 967400 :=
  FiniteIntervals.of_fin 967200 200 complete_chunk4836

lemma complete_chunk4837 : ∀ i : Fin 200, Compatible (967400 + i.val) →
    (table.lookup (967400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4837 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 967400 967600 :=
  FiniteIntervals.of_fin 967400 200 complete_chunk4837

lemma complete_chunk4838 : ∀ i : Fin 200, Compatible (967600 + i.val) →
    (table.lookup (967600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4838 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 967600 967800 :=
  FiniteIntervals.of_fin 967600 200 complete_chunk4838

lemma complete_chunk4839 : ∀ i : Fin 200, Compatible (967800 + i.val) →
    (table.lookup (967800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4839 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 967800 968000 :=
  FiniteIntervals.of_fin 967800 200 complete_chunk4839

#print axioms interval_chunk4830
end Erdos184Work.PureFiveFilter4
