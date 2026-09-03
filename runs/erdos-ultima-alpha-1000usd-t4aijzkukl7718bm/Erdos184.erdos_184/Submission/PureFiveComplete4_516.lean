import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5160 : ∀ i : Fin 200, Compatible (1032000 + i.val) →
    (table.lookup (1032000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5160 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1032000 1032200 :=
  FiniteIntervals.of_fin 1032000 200 complete_chunk5160

lemma complete_chunk5161 : ∀ i : Fin 200, Compatible (1032200 + i.val) →
    (table.lookup (1032200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5161 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1032200 1032400 :=
  FiniteIntervals.of_fin 1032200 200 complete_chunk5161

lemma complete_chunk5162 : ∀ i : Fin 200, Compatible (1032400 + i.val) →
    (table.lookup (1032400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5162 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1032400 1032600 :=
  FiniteIntervals.of_fin 1032400 200 complete_chunk5162

lemma complete_chunk5163 : ∀ i : Fin 200, Compatible (1032600 + i.val) →
    (table.lookup (1032600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5163 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1032600 1032800 :=
  FiniteIntervals.of_fin 1032600 200 complete_chunk5163

lemma complete_chunk5164 : ∀ i : Fin 200, Compatible (1032800 + i.val) →
    (table.lookup (1032800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5164 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1032800 1033000 :=
  FiniteIntervals.of_fin 1032800 200 complete_chunk5164

lemma complete_chunk5165 : ∀ i : Fin 200, Compatible (1033000 + i.val) →
    (table.lookup (1033000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5165 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1033000 1033200 :=
  FiniteIntervals.of_fin 1033000 200 complete_chunk5165

lemma complete_chunk5166 : ∀ i : Fin 200, Compatible (1033200 + i.val) →
    (table.lookup (1033200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5166 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1033200 1033400 :=
  FiniteIntervals.of_fin 1033200 200 complete_chunk5166

lemma complete_chunk5167 : ∀ i : Fin 200, Compatible (1033400 + i.val) →
    (table.lookup (1033400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5167 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1033400 1033600 :=
  FiniteIntervals.of_fin 1033400 200 complete_chunk5167

lemma complete_chunk5168 : ∀ i : Fin 200, Compatible (1033600 + i.val) →
    (table.lookup (1033600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5168 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1033600 1033800 :=
  FiniteIntervals.of_fin 1033600 200 complete_chunk5168

lemma complete_chunk5169 : ∀ i : Fin 200, Compatible (1033800 + i.val) →
    (table.lookup (1033800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5169 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1033800 1034000 :=
  FiniteIntervals.of_fin 1033800 200 complete_chunk5169

#print axioms interval_chunk5160
end Erdos184Work.PureFiveFilter4
