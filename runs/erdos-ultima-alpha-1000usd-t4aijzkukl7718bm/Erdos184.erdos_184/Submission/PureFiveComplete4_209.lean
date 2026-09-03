import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2090 : ∀ i : Fin 200, Compatible (418000 + i.val) →
    (table.lookup (418000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2090 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 418000 418200 :=
  FiniteIntervals.of_fin 418000 200 complete_chunk2090

lemma complete_chunk2091 : ∀ i : Fin 200, Compatible (418200 + i.val) →
    (table.lookup (418200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2091 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 418200 418400 :=
  FiniteIntervals.of_fin 418200 200 complete_chunk2091

lemma complete_chunk2092 : ∀ i : Fin 200, Compatible (418400 + i.val) →
    (table.lookup (418400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2092 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 418400 418600 :=
  FiniteIntervals.of_fin 418400 200 complete_chunk2092

lemma complete_chunk2093 : ∀ i : Fin 200, Compatible (418600 + i.val) →
    (table.lookup (418600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2093 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 418600 418800 :=
  FiniteIntervals.of_fin 418600 200 complete_chunk2093

lemma complete_chunk2094 : ∀ i : Fin 200, Compatible (418800 + i.val) →
    (table.lookup (418800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2094 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 418800 419000 :=
  FiniteIntervals.of_fin 418800 200 complete_chunk2094

lemma complete_chunk2095 : ∀ i : Fin 200, Compatible (419000 + i.val) →
    (table.lookup (419000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2095 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 419000 419200 :=
  FiniteIntervals.of_fin 419000 200 complete_chunk2095

lemma complete_chunk2096 : ∀ i : Fin 200, Compatible (419200 + i.val) →
    (table.lookup (419200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2096 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 419200 419400 :=
  FiniteIntervals.of_fin 419200 200 complete_chunk2096

lemma complete_chunk2097 : ∀ i : Fin 200, Compatible (419400 + i.val) →
    (table.lookup (419400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2097 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 419400 419600 :=
  FiniteIntervals.of_fin 419400 200 complete_chunk2097

lemma complete_chunk2098 : ∀ i : Fin 200, Compatible (419600 + i.val) →
    (table.lookup (419600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2098 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 419600 419800 :=
  FiniteIntervals.of_fin 419600 200 complete_chunk2098

lemma complete_chunk2099 : ∀ i : Fin 200, Compatible (419800 + i.val) →
    (table.lookup (419800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2099 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 419800 420000 :=
  FiniteIntervals.of_fin 419800 200 complete_chunk2099

#print axioms interval_chunk2090
end Erdos184Work.PureFiveFilter4
