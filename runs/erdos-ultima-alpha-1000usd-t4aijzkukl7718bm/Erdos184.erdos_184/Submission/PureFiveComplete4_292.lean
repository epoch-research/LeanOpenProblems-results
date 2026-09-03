import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2920 : ∀ i : Fin 200, Compatible (584000 + i.val) →
    (table.lookup (584000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2920 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 584000 584200 :=
  FiniteIntervals.of_fin 584000 200 complete_chunk2920

lemma complete_chunk2921 : ∀ i : Fin 200, Compatible (584200 + i.val) →
    (table.lookup (584200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2921 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 584200 584400 :=
  FiniteIntervals.of_fin 584200 200 complete_chunk2921

lemma complete_chunk2922 : ∀ i : Fin 200, Compatible (584400 + i.val) →
    (table.lookup (584400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2922 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 584400 584600 :=
  FiniteIntervals.of_fin 584400 200 complete_chunk2922

lemma complete_chunk2923 : ∀ i : Fin 200, Compatible (584600 + i.val) →
    (table.lookup (584600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2923 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 584600 584800 :=
  FiniteIntervals.of_fin 584600 200 complete_chunk2923

lemma complete_chunk2924 : ∀ i : Fin 200, Compatible (584800 + i.val) →
    (table.lookup (584800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2924 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 584800 585000 :=
  FiniteIntervals.of_fin 584800 200 complete_chunk2924

lemma complete_chunk2925 : ∀ i : Fin 200, Compatible (585000 + i.val) →
    (table.lookup (585000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2925 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 585000 585200 :=
  FiniteIntervals.of_fin 585000 200 complete_chunk2925

lemma complete_chunk2926 : ∀ i : Fin 200, Compatible (585200 + i.val) →
    (table.lookup (585200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2926 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 585200 585400 :=
  FiniteIntervals.of_fin 585200 200 complete_chunk2926

lemma complete_chunk2927 : ∀ i : Fin 200, Compatible (585400 + i.val) →
    (table.lookup (585400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2927 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 585400 585600 :=
  FiniteIntervals.of_fin 585400 200 complete_chunk2927

lemma complete_chunk2928 : ∀ i : Fin 200, Compatible (585600 + i.val) →
    (table.lookup (585600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2928 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 585600 585800 :=
  FiniteIntervals.of_fin 585600 200 complete_chunk2928

lemma complete_chunk2929 : ∀ i : Fin 200, Compatible (585800 + i.val) →
    (table.lookup (585800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2929 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 585800 586000 :=
  FiniteIntervals.of_fin 585800 200 complete_chunk2929

#print axioms interval_chunk2920
end Erdos184Work.PureFiveFilter4
