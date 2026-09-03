import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1980 : ∀ i : Fin 200, Compatible (396000 + i.val) →
    (table.lookup (396000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1980 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 396000 396200 :=
  FiniteIntervals.of_fin 396000 200 complete_chunk1980

lemma complete_chunk1981 : ∀ i : Fin 200, Compatible (396200 + i.val) →
    (table.lookup (396200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1981 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 396200 396400 :=
  FiniteIntervals.of_fin 396200 200 complete_chunk1981

lemma complete_chunk1982 : ∀ i : Fin 200, Compatible (396400 + i.val) →
    (table.lookup (396400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1982 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 396400 396600 :=
  FiniteIntervals.of_fin 396400 200 complete_chunk1982

lemma complete_chunk1983 : ∀ i : Fin 200, Compatible (396600 + i.val) →
    (table.lookup (396600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1983 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 396600 396800 :=
  FiniteIntervals.of_fin 396600 200 complete_chunk1983

lemma complete_chunk1984 : ∀ i : Fin 200, Compatible (396800 + i.val) →
    (table.lookup (396800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1984 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 396800 397000 :=
  FiniteIntervals.of_fin 396800 200 complete_chunk1984

lemma complete_chunk1985 : ∀ i : Fin 200, Compatible (397000 + i.val) →
    (table.lookup (397000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1985 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 397000 397200 :=
  FiniteIntervals.of_fin 397000 200 complete_chunk1985

lemma complete_chunk1986 : ∀ i : Fin 200, Compatible (397200 + i.val) →
    (table.lookup (397200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1986 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 397200 397400 :=
  FiniteIntervals.of_fin 397200 200 complete_chunk1986

lemma complete_chunk1987 : ∀ i : Fin 200, Compatible (397400 + i.val) →
    (table.lookup (397400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1987 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 397400 397600 :=
  FiniteIntervals.of_fin 397400 200 complete_chunk1987

lemma complete_chunk1988 : ∀ i : Fin 200, Compatible (397600 + i.val) →
    (table.lookup (397600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1988 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 397600 397800 :=
  FiniteIntervals.of_fin 397600 200 complete_chunk1988

lemma complete_chunk1989 : ∀ i : Fin 200, Compatible (397800 + i.val) →
    (table.lookup (397800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1989 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 397800 398000 :=
  FiniteIntervals.of_fin 397800 200 complete_chunk1989

#print axioms interval_chunk1980
end Erdos184Work.PureFiveFilter4
