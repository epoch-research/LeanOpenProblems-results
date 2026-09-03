import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2050 : ∀ i : Fin 200, Compatible (410000 + i.val) →
    (table.lookup (410000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2050 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 410000 410200 :=
  FiniteIntervals.of_fin 410000 200 complete_chunk2050

lemma complete_chunk2051 : ∀ i : Fin 200, Compatible (410200 + i.val) →
    (table.lookup (410200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2051 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 410200 410400 :=
  FiniteIntervals.of_fin 410200 200 complete_chunk2051

lemma complete_chunk2052 : ∀ i : Fin 200, Compatible (410400 + i.val) →
    (table.lookup (410400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2052 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 410400 410600 :=
  FiniteIntervals.of_fin 410400 200 complete_chunk2052

lemma complete_chunk2053 : ∀ i : Fin 200, Compatible (410600 + i.val) →
    (table.lookup (410600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2053 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 410600 410800 :=
  FiniteIntervals.of_fin 410600 200 complete_chunk2053

lemma complete_chunk2054 : ∀ i : Fin 200, Compatible (410800 + i.val) →
    (table.lookup (410800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2054 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 410800 411000 :=
  FiniteIntervals.of_fin 410800 200 complete_chunk2054

lemma complete_chunk2055 : ∀ i : Fin 200, Compatible (411000 + i.val) →
    (table.lookup (411000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2055 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 411000 411200 :=
  FiniteIntervals.of_fin 411000 200 complete_chunk2055

lemma complete_chunk2056 : ∀ i : Fin 200, Compatible (411200 + i.val) →
    (table.lookup (411200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2056 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 411200 411400 :=
  FiniteIntervals.of_fin 411200 200 complete_chunk2056

lemma complete_chunk2057 : ∀ i : Fin 200, Compatible (411400 + i.val) →
    (table.lookup (411400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2057 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 411400 411600 :=
  FiniteIntervals.of_fin 411400 200 complete_chunk2057

lemma complete_chunk2058 : ∀ i : Fin 200, Compatible (411600 + i.val) →
    (table.lookup (411600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2058 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 411600 411800 :=
  FiniteIntervals.of_fin 411600 200 complete_chunk2058

lemma complete_chunk2059 : ∀ i : Fin 200, Compatible (411800 + i.val) →
    (table.lookup (411800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2059 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 411800 412000 :=
  FiniteIntervals.of_fin 411800 200 complete_chunk2059

#print axioms interval_chunk2050
end Erdos184Work.PureFiveFilter4
