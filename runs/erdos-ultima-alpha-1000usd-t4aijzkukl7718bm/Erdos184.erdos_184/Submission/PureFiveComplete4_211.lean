import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2110 : ∀ i : Fin 200, Compatible (422000 + i.val) →
    (table.lookup (422000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2110 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 422000 422200 :=
  FiniteIntervals.of_fin 422000 200 complete_chunk2110

lemma complete_chunk2111 : ∀ i : Fin 200, Compatible (422200 + i.val) →
    (table.lookup (422200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2111 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 422200 422400 :=
  FiniteIntervals.of_fin 422200 200 complete_chunk2111

lemma complete_chunk2112 : ∀ i : Fin 200, Compatible (422400 + i.val) →
    (table.lookup (422400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2112 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 422400 422600 :=
  FiniteIntervals.of_fin 422400 200 complete_chunk2112

lemma complete_chunk2113 : ∀ i : Fin 200, Compatible (422600 + i.val) →
    (table.lookup (422600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2113 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 422600 422800 :=
  FiniteIntervals.of_fin 422600 200 complete_chunk2113

lemma complete_chunk2114 : ∀ i : Fin 200, Compatible (422800 + i.val) →
    (table.lookup (422800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2114 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 422800 423000 :=
  FiniteIntervals.of_fin 422800 200 complete_chunk2114

lemma complete_chunk2115 : ∀ i : Fin 200, Compatible (423000 + i.val) →
    (table.lookup (423000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2115 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 423000 423200 :=
  FiniteIntervals.of_fin 423000 200 complete_chunk2115

lemma complete_chunk2116 : ∀ i : Fin 200, Compatible (423200 + i.val) →
    (table.lookup (423200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2116 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 423200 423400 :=
  FiniteIntervals.of_fin 423200 200 complete_chunk2116

lemma complete_chunk2117 : ∀ i : Fin 200, Compatible (423400 + i.val) →
    (table.lookup (423400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2117 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 423400 423600 :=
  FiniteIntervals.of_fin 423400 200 complete_chunk2117

lemma complete_chunk2118 : ∀ i : Fin 200, Compatible (423600 + i.val) →
    (table.lookup (423600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2118 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 423600 423800 :=
  FiniteIntervals.of_fin 423600 200 complete_chunk2118

lemma complete_chunk2119 : ∀ i : Fin 200, Compatible (423800 + i.val) →
    (table.lookup (423800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2119 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 423800 424000 :=
  FiniteIntervals.of_fin 423800 200 complete_chunk2119

#print axioms interval_chunk2110
end Erdos184Work.PureFiveFilter4
