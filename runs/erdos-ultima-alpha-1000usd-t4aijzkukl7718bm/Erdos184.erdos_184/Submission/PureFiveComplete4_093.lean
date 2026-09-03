import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk930 : ∀ i : Fin 200, Compatible (186000 + i.val) →
    (table.lookup (186000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk930 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 186000 186200 :=
  FiniteIntervals.of_fin 186000 200 complete_chunk930

lemma complete_chunk931 : ∀ i : Fin 200, Compatible (186200 + i.val) →
    (table.lookup (186200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk931 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 186200 186400 :=
  FiniteIntervals.of_fin 186200 200 complete_chunk931

lemma complete_chunk932 : ∀ i : Fin 200, Compatible (186400 + i.val) →
    (table.lookup (186400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk932 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 186400 186600 :=
  FiniteIntervals.of_fin 186400 200 complete_chunk932

lemma complete_chunk933 : ∀ i : Fin 200, Compatible (186600 + i.val) →
    (table.lookup (186600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk933 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 186600 186800 :=
  FiniteIntervals.of_fin 186600 200 complete_chunk933

lemma complete_chunk934 : ∀ i : Fin 200, Compatible (186800 + i.val) →
    (table.lookup (186800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk934 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 186800 187000 :=
  FiniteIntervals.of_fin 186800 200 complete_chunk934

lemma complete_chunk935 : ∀ i : Fin 200, Compatible (187000 + i.val) →
    (table.lookup (187000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk935 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 187000 187200 :=
  FiniteIntervals.of_fin 187000 200 complete_chunk935

lemma complete_chunk936 : ∀ i : Fin 200, Compatible (187200 + i.val) →
    (table.lookup (187200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk936 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 187200 187400 :=
  FiniteIntervals.of_fin 187200 200 complete_chunk936

lemma complete_chunk937 : ∀ i : Fin 200, Compatible (187400 + i.val) →
    (table.lookup (187400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk937 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 187400 187600 :=
  FiniteIntervals.of_fin 187400 200 complete_chunk937

lemma complete_chunk938 : ∀ i : Fin 200, Compatible (187600 + i.val) →
    (table.lookup (187600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk938 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 187600 187800 :=
  FiniteIntervals.of_fin 187600 200 complete_chunk938

lemma complete_chunk939 : ∀ i : Fin 200, Compatible (187800 + i.val) →
    (table.lookup (187800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk939 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 187800 188000 :=
  FiniteIntervals.of_fin 187800 200 complete_chunk939

#print axioms interval_chunk930
end Erdos184Work.PureFiveFilter4
