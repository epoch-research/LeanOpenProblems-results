import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2150 : ∀ i : Fin 200, Compatible (430000 + i.val) →
    (table.lookup (430000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2150 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 430000 430200 :=
  FiniteIntervals.of_fin 430000 200 complete_chunk2150

lemma complete_chunk2151 : ∀ i : Fin 200, Compatible (430200 + i.val) →
    (table.lookup (430200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2151 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 430200 430400 :=
  FiniteIntervals.of_fin 430200 200 complete_chunk2151

lemma complete_chunk2152 : ∀ i : Fin 200, Compatible (430400 + i.val) →
    (table.lookup (430400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2152 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 430400 430600 :=
  FiniteIntervals.of_fin 430400 200 complete_chunk2152

lemma complete_chunk2153 : ∀ i : Fin 200, Compatible (430600 + i.val) →
    (table.lookup (430600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2153 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 430600 430800 :=
  FiniteIntervals.of_fin 430600 200 complete_chunk2153

lemma complete_chunk2154 : ∀ i : Fin 200, Compatible (430800 + i.val) →
    (table.lookup (430800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2154 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 430800 431000 :=
  FiniteIntervals.of_fin 430800 200 complete_chunk2154

lemma complete_chunk2155 : ∀ i : Fin 200, Compatible (431000 + i.val) →
    (table.lookup (431000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2155 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 431000 431200 :=
  FiniteIntervals.of_fin 431000 200 complete_chunk2155

lemma complete_chunk2156 : ∀ i : Fin 200, Compatible (431200 + i.val) →
    (table.lookup (431200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2156 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 431200 431400 :=
  FiniteIntervals.of_fin 431200 200 complete_chunk2156

lemma complete_chunk2157 : ∀ i : Fin 200, Compatible (431400 + i.val) →
    (table.lookup (431400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2157 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 431400 431600 :=
  FiniteIntervals.of_fin 431400 200 complete_chunk2157

lemma complete_chunk2158 : ∀ i : Fin 200, Compatible (431600 + i.val) →
    (table.lookup (431600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2158 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 431600 431800 :=
  FiniteIntervals.of_fin 431600 200 complete_chunk2158

lemma complete_chunk2159 : ∀ i : Fin 200, Compatible (431800 + i.val) →
    (table.lookup (431800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2159 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 431800 432000 :=
  FiniteIntervals.of_fin 431800 200 complete_chunk2159

#print axioms interval_chunk2150
end Erdos184Work.PureFiveFilter4
