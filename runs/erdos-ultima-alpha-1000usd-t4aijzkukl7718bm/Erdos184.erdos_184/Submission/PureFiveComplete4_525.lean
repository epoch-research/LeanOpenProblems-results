import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5250 : ∀ i : Fin 200, Compatible (1050000 + i.val) →
    (table.lookup (1050000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5250 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1050000 1050200 :=
  FiniteIntervals.of_fin 1050000 200 complete_chunk5250

lemma complete_chunk5251 : ∀ i : Fin 200, Compatible (1050200 + i.val) →
    (table.lookup (1050200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5251 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1050200 1050400 :=
  FiniteIntervals.of_fin 1050200 200 complete_chunk5251

lemma complete_chunk5252 : ∀ i : Fin 200, Compatible (1050400 + i.val) →
    (table.lookup (1050400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5252 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1050400 1050600 :=
  FiniteIntervals.of_fin 1050400 200 complete_chunk5252

lemma complete_chunk5253 : ∀ i : Fin 200, Compatible (1050600 + i.val) →
    (table.lookup (1050600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5253 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1050600 1050800 :=
  FiniteIntervals.of_fin 1050600 200 complete_chunk5253

lemma complete_chunk5254 : ∀ i : Fin 200, Compatible (1050800 + i.val) →
    (table.lookup (1050800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5254 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1050800 1051000 :=
  FiniteIntervals.of_fin 1050800 200 complete_chunk5254

lemma complete_chunk5255 : ∀ i : Fin 200, Compatible (1051000 + i.val) →
    (table.lookup (1051000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5255 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1051000 1051200 :=
  FiniteIntervals.of_fin 1051000 200 complete_chunk5255

lemma complete_chunk5256 : ∀ i : Fin 200, Compatible (1051200 + i.val) →
    (table.lookup (1051200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5256 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1051200 1051400 :=
  FiniteIntervals.of_fin 1051200 200 complete_chunk5256

lemma complete_chunk5257 : ∀ i : Fin 200, Compatible (1051400 + i.val) →
    (table.lookup (1051400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5257 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1051400 1051600 :=
  FiniteIntervals.of_fin 1051400 200 complete_chunk5257

lemma complete_chunk5258 : ∀ i : Fin 200, Compatible (1051600 + i.val) →
    (table.lookup (1051600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5258 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1051600 1051800 :=
  FiniteIntervals.of_fin 1051600 200 complete_chunk5258

lemma complete_chunk5259 : ∀ i : Fin 200, Compatible (1051800 + i.val) →
    (table.lookup (1051800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5259 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1051800 1052000 :=
  FiniteIntervals.of_fin 1051800 200 complete_chunk5259

#print axioms interval_chunk5250
end Erdos184Work.PureFiveFilter4
