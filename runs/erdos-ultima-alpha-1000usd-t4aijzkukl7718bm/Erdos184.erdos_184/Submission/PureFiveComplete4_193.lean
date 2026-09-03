import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1930 : ∀ i : Fin 200, Compatible (386000 + i.val) →
    (table.lookup (386000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1930 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 386000 386200 :=
  FiniteIntervals.of_fin 386000 200 complete_chunk1930

lemma complete_chunk1931 : ∀ i : Fin 200, Compatible (386200 + i.val) →
    (table.lookup (386200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1931 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 386200 386400 :=
  FiniteIntervals.of_fin 386200 200 complete_chunk1931

lemma complete_chunk1932 : ∀ i : Fin 200, Compatible (386400 + i.val) →
    (table.lookup (386400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1932 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 386400 386600 :=
  FiniteIntervals.of_fin 386400 200 complete_chunk1932

lemma complete_chunk1933 : ∀ i : Fin 200, Compatible (386600 + i.val) →
    (table.lookup (386600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1933 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 386600 386800 :=
  FiniteIntervals.of_fin 386600 200 complete_chunk1933

lemma complete_chunk1934 : ∀ i : Fin 200, Compatible (386800 + i.val) →
    (table.lookup (386800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1934 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 386800 387000 :=
  FiniteIntervals.of_fin 386800 200 complete_chunk1934

lemma complete_chunk1935 : ∀ i : Fin 200, Compatible (387000 + i.val) →
    (table.lookup (387000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1935 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 387000 387200 :=
  FiniteIntervals.of_fin 387000 200 complete_chunk1935

lemma complete_chunk1936 : ∀ i : Fin 200, Compatible (387200 + i.val) →
    (table.lookup (387200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1936 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 387200 387400 :=
  FiniteIntervals.of_fin 387200 200 complete_chunk1936

lemma complete_chunk1937 : ∀ i : Fin 200, Compatible (387400 + i.val) →
    (table.lookup (387400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1937 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 387400 387600 :=
  FiniteIntervals.of_fin 387400 200 complete_chunk1937

lemma complete_chunk1938 : ∀ i : Fin 200, Compatible (387600 + i.val) →
    (table.lookup (387600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1938 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 387600 387800 :=
  FiniteIntervals.of_fin 387600 200 complete_chunk1938

lemma complete_chunk1939 : ∀ i : Fin 200, Compatible (387800 + i.val) →
    (table.lookup (387800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1939 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 387800 388000 :=
  FiniteIntervals.of_fin 387800 200 complete_chunk1939

#print axioms interval_chunk1930
end Erdos184Work.PureFiveFilter4
