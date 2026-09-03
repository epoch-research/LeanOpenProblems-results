import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5930 : ∀ i : Fin 200, Compatible (1186000 + i.val) →
    (table.lookup (1186000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5930 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1186000 1186200 :=
  FiniteIntervals.of_fin 1186000 200 complete_chunk5930

lemma complete_chunk5931 : ∀ i : Fin 200, Compatible (1186200 + i.val) →
    (table.lookup (1186200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5931 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1186200 1186400 :=
  FiniteIntervals.of_fin 1186200 200 complete_chunk5931

lemma complete_chunk5932 : ∀ i : Fin 200, Compatible (1186400 + i.val) →
    (table.lookup (1186400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5932 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1186400 1186600 :=
  FiniteIntervals.of_fin 1186400 200 complete_chunk5932

lemma complete_chunk5933 : ∀ i : Fin 200, Compatible (1186600 + i.val) →
    (table.lookup (1186600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5933 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1186600 1186800 :=
  FiniteIntervals.of_fin 1186600 200 complete_chunk5933

lemma complete_chunk5934 : ∀ i : Fin 200, Compatible (1186800 + i.val) →
    (table.lookup (1186800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5934 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1186800 1187000 :=
  FiniteIntervals.of_fin 1186800 200 complete_chunk5934

lemma complete_chunk5935 : ∀ i : Fin 200, Compatible (1187000 + i.val) →
    (table.lookup (1187000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5935 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1187000 1187200 :=
  FiniteIntervals.of_fin 1187000 200 complete_chunk5935

lemma complete_chunk5936 : ∀ i : Fin 200, Compatible (1187200 + i.val) →
    (table.lookup (1187200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5936 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1187200 1187400 :=
  FiniteIntervals.of_fin 1187200 200 complete_chunk5936

lemma complete_chunk5937 : ∀ i : Fin 200, Compatible (1187400 + i.val) →
    (table.lookup (1187400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5937 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1187400 1187600 :=
  FiniteIntervals.of_fin 1187400 200 complete_chunk5937

lemma complete_chunk5938 : ∀ i : Fin 200, Compatible (1187600 + i.val) →
    (table.lookup (1187600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5938 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1187600 1187800 :=
  FiniteIntervals.of_fin 1187600 200 complete_chunk5938

lemma complete_chunk5939 : ∀ i : Fin 200, Compatible (1187800 + i.val) →
    (table.lookup (1187800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5939 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1187800 1188000 :=
  FiniteIntervals.of_fin 1187800 200 complete_chunk5939

#print axioms interval_chunk5930
end Erdos184Work.PureFiveFilter4
