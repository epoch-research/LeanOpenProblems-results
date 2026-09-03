import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5070 : ∀ i : Fin 200, Compatible (1014000 + i.val) →
    (table.lookup (1014000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5070 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1014000 1014200 :=
  FiniteIntervals.of_fin 1014000 200 complete_chunk5070

lemma complete_chunk5071 : ∀ i : Fin 200, Compatible (1014200 + i.val) →
    (table.lookup (1014200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5071 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1014200 1014400 :=
  FiniteIntervals.of_fin 1014200 200 complete_chunk5071

lemma complete_chunk5072 : ∀ i : Fin 200, Compatible (1014400 + i.val) →
    (table.lookup (1014400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5072 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1014400 1014600 :=
  FiniteIntervals.of_fin 1014400 200 complete_chunk5072

lemma complete_chunk5073 : ∀ i : Fin 200, Compatible (1014600 + i.val) →
    (table.lookup (1014600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5073 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1014600 1014800 :=
  FiniteIntervals.of_fin 1014600 200 complete_chunk5073

lemma complete_chunk5074 : ∀ i : Fin 200, Compatible (1014800 + i.val) →
    (table.lookup (1014800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5074 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1014800 1015000 :=
  FiniteIntervals.of_fin 1014800 200 complete_chunk5074

lemma complete_chunk5075 : ∀ i : Fin 200, Compatible (1015000 + i.val) →
    (table.lookup (1015000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5075 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1015000 1015200 :=
  FiniteIntervals.of_fin 1015000 200 complete_chunk5075

lemma complete_chunk5076 : ∀ i : Fin 200, Compatible (1015200 + i.val) →
    (table.lookup (1015200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5076 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1015200 1015400 :=
  FiniteIntervals.of_fin 1015200 200 complete_chunk5076

lemma complete_chunk5077 : ∀ i : Fin 200, Compatible (1015400 + i.val) →
    (table.lookup (1015400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5077 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1015400 1015600 :=
  FiniteIntervals.of_fin 1015400 200 complete_chunk5077

lemma complete_chunk5078 : ∀ i : Fin 200, Compatible (1015600 + i.val) →
    (table.lookup (1015600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5078 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1015600 1015800 :=
  FiniteIntervals.of_fin 1015600 200 complete_chunk5078

lemma complete_chunk5079 : ∀ i : Fin 200, Compatible (1015800 + i.val) →
    (table.lookup (1015800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5079 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1015800 1016000 :=
  FiniteIntervals.of_fin 1015800 200 complete_chunk5079

#print axioms interval_chunk5070
end Erdos184Work.PureFiveFilter4
