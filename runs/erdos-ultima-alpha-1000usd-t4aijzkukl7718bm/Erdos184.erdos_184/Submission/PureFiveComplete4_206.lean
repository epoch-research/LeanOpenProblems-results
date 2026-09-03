import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2060 : ∀ i : Fin 200, Compatible (412000 + i.val) →
    (table.lookup (412000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2060 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 412000 412200 :=
  FiniteIntervals.of_fin 412000 200 complete_chunk2060

lemma complete_chunk2061 : ∀ i : Fin 200, Compatible (412200 + i.val) →
    (table.lookup (412200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2061 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 412200 412400 :=
  FiniteIntervals.of_fin 412200 200 complete_chunk2061

lemma complete_chunk2062 : ∀ i : Fin 200, Compatible (412400 + i.val) →
    (table.lookup (412400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2062 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 412400 412600 :=
  FiniteIntervals.of_fin 412400 200 complete_chunk2062

lemma complete_chunk2063 : ∀ i : Fin 200, Compatible (412600 + i.val) →
    (table.lookup (412600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2063 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 412600 412800 :=
  FiniteIntervals.of_fin 412600 200 complete_chunk2063

lemma complete_chunk2064 : ∀ i : Fin 200, Compatible (412800 + i.val) →
    (table.lookup (412800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2064 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 412800 413000 :=
  FiniteIntervals.of_fin 412800 200 complete_chunk2064

lemma complete_chunk2065 : ∀ i : Fin 200, Compatible (413000 + i.val) →
    (table.lookup (413000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2065 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 413000 413200 :=
  FiniteIntervals.of_fin 413000 200 complete_chunk2065

lemma complete_chunk2066 : ∀ i : Fin 200, Compatible (413200 + i.val) →
    (table.lookup (413200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2066 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 413200 413400 :=
  FiniteIntervals.of_fin 413200 200 complete_chunk2066

lemma complete_chunk2067 : ∀ i : Fin 200, Compatible (413400 + i.val) →
    (table.lookup (413400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2067 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 413400 413600 :=
  FiniteIntervals.of_fin 413400 200 complete_chunk2067

lemma complete_chunk2068 : ∀ i : Fin 200, Compatible (413600 + i.val) →
    (table.lookup (413600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2068 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 413600 413800 :=
  FiniteIntervals.of_fin 413600 200 complete_chunk2068

lemma complete_chunk2069 : ∀ i : Fin 200, Compatible (413800 + i.val) →
    (table.lookup (413800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2069 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 413800 414000 :=
  FiniteIntervals.of_fin 413800 200 complete_chunk2069

#print axioms interval_chunk2060
end Erdos184Work.PureFiveFilter4
