import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2070 : ∀ i : Fin 200, Compatible (414000 + i.val) →
    (table.lookup (414000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2070 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 414000 414200 :=
  FiniteIntervals.of_fin 414000 200 complete_chunk2070

lemma complete_chunk2071 : ∀ i : Fin 200, Compatible (414200 + i.val) →
    (table.lookup (414200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2071 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 414200 414400 :=
  FiniteIntervals.of_fin 414200 200 complete_chunk2071

lemma complete_chunk2072 : ∀ i : Fin 200, Compatible (414400 + i.val) →
    (table.lookup (414400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2072 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 414400 414600 :=
  FiniteIntervals.of_fin 414400 200 complete_chunk2072

lemma complete_chunk2073 : ∀ i : Fin 200, Compatible (414600 + i.val) →
    (table.lookup (414600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2073 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 414600 414800 :=
  FiniteIntervals.of_fin 414600 200 complete_chunk2073

lemma complete_chunk2074 : ∀ i : Fin 200, Compatible (414800 + i.val) →
    (table.lookup (414800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2074 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 414800 415000 :=
  FiniteIntervals.of_fin 414800 200 complete_chunk2074

lemma complete_chunk2075 : ∀ i : Fin 200, Compatible (415000 + i.val) →
    (table.lookup (415000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2075 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 415000 415200 :=
  FiniteIntervals.of_fin 415000 200 complete_chunk2075

lemma complete_chunk2076 : ∀ i : Fin 200, Compatible (415200 + i.val) →
    (table.lookup (415200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2076 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 415200 415400 :=
  FiniteIntervals.of_fin 415200 200 complete_chunk2076

lemma complete_chunk2077 : ∀ i : Fin 200, Compatible (415400 + i.val) →
    (table.lookup (415400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2077 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 415400 415600 :=
  FiniteIntervals.of_fin 415400 200 complete_chunk2077

lemma complete_chunk2078 : ∀ i : Fin 200, Compatible (415600 + i.val) →
    (table.lookup (415600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2078 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 415600 415800 :=
  FiniteIntervals.of_fin 415600 200 complete_chunk2078

lemma complete_chunk2079 : ∀ i : Fin 200, Compatible (415800 + i.val) →
    (table.lookup (415800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2079 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 415800 416000 :=
  FiniteIntervals.of_fin 415800 200 complete_chunk2079

#print axioms interval_chunk2070
end Erdos184Work.PureFiveFilter4
