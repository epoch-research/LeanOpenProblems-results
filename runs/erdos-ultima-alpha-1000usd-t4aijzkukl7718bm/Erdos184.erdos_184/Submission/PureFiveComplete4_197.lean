import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1970 : ∀ i : Fin 200, Compatible (394000 + i.val) →
    (table.lookup (394000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1970 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 394000 394200 :=
  FiniteIntervals.of_fin 394000 200 complete_chunk1970

lemma complete_chunk1971 : ∀ i : Fin 200, Compatible (394200 + i.val) →
    (table.lookup (394200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1971 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 394200 394400 :=
  FiniteIntervals.of_fin 394200 200 complete_chunk1971

lemma complete_chunk1972 : ∀ i : Fin 200, Compatible (394400 + i.val) →
    (table.lookup (394400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1972 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 394400 394600 :=
  FiniteIntervals.of_fin 394400 200 complete_chunk1972

lemma complete_chunk1973 : ∀ i : Fin 200, Compatible (394600 + i.val) →
    (table.lookup (394600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1973 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 394600 394800 :=
  FiniteIntervals.of_fin 394600 200 complete_chunk1973

lemma complete_chunk1974 : ∀ i : Fin 200, Compatible (394800 + i.val) →
    (table.lookup (394800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1974 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 394800 395000 :=
  FiniteIntervals.of_fin 394800 200 complete_chunk1974

lemma complete_chunk1975 : ∀ i : Fin 200, Compatible (395000 + i.val) →
    (table.lookup (395000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1975 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 395000 395200 :=
  FiniteIntervals.of_fin 395000 200 complete_chunk1975

lemma complete_chunk1976 : ∀ i : Fin 200, Compatible (395200 + i.val) →
    (table.lookup (395200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1976 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 395200 395400 :=
  FiniteIntervals.of_fin 395200 200 complete_chunk1976

lemma complete_chunk1977 : ∀ i : Fin 200, Compatible (395400 + i.val) →
    (table.lookup (395400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1977 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 395400 395600 :=
  FiniteIntervals.of_fin 395400 200 complete_chunk1977

lemma complete_chunk1978 : ∀ i : Fin 200, Compatible (395600 + i.val) →
    (table.lookup (395600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1978 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 395600 395800 :=
  FiniteIntervals.of_fin 395600 200 complete_chunk1978

lemma complete_chunk1979 : ∀ i : Fin 200, Compatible (395800 + i.val) →
    (table.lookup (395800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1979 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 395800 396000 :=
  FiniteIntervals.of_fin 395800 200 complete_chunk1979

#print axioms interval_chunk1970
end Erdos184Work.PureFiveFilter4
