import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1920 : ∀ i : Fin 200, Compatible (384000 + i.val) →
    (table.lookup (384000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1920 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 384000 384200 :=
  FiniteIntervals.of_fin 384000 200 complete_chunk1920

lemma complete_chunk1921 : ∀ i : Fin 200, Compatible (384200 + i.val) →
    (table.lookup (384200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1921 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 384200 384400 :=
  FiniteIntervals.of_fin 384200 200 complete_chunk1921

lemma complete_chunk1922 : ∀ i : Fin 200, Compatible (384400 + i.val) →
    (table.lookup (384400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1922 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 384400 384600 :=
  FiniteIntervals.of_fin 384400 200 complete_chunk1922

lemma complete_chunk1923 : ∀ i : Fin 200, Compatible (384600 + i.val) →
    (table.lookup (384600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1923 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 384600 384800 :=
  FiniteIntervals.of_fin 384600 200 complete_chunk1923

lemma complete_chunk1924 : ∀ i : Fin 200, Compatible (384800 + i.val) →
    (table.lookup (384800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1924 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 384800 385000 :=
  FiniteIntervals.of_fin 384800 200 complete_chunk1924

lemma complete_chunk1925 : ∀ i : Fin 200, Compatible (385000 + i.val) →
    (table.lookup (385000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1925 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 385000 385200 :=
  FiniteIntervals.of_fin 385000 200 complete_chunk1925

lemma complete_chunk1926 : ∀ i : Fin 200, Compatible (385200 + i.val) →
    (table.lookup (385200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1926 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 385200 385400 :=
  FiniteIntervals.of_fin 385200 200 complete_chunk1926

lemma complete_chunk1927 : ∀ i : Fin 200, Compatible (385400 + i.val) →
    (table.lookup (385400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1927 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 385400 385600 :=
  FiniteIntervals.of_fin 385400 200 complete_chunk1927

lemma complete_chunk1928 : ∀ i : Fin 200, Compatible (385600 + i.val) →
    (table.lookup (385600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1928 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 385600 385800 :=
  FiniteIntervals.of_fin 385600 200 complete_chunk1928

lemma complete_chunk1929 : ∀ i : Fin 200, Compatible (385800 + i.val) →
    (table.lookup (385800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1929 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 385800 386000 :=
  FiniteIntervals.of_fin 385800 200 complete_chunk1929

#print axioms interval_chunk1920
end Erdos184Work.PureFiveFilter4
