import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5170 : ∀ i : Fin 200, Compatible (1034000 + i.val) →
    (table.lookup (1034000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5170 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1034000 1034200 :=
  FiniteIntervals.of_fin 1034000 200 complete_chunk5170

lemma complete_chunk5171 : ∀ i : Fin 200, Compatible (1034200 + i.val) →
    (table.lookup (1034200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5171 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1034200 1034400 :=
  FiniteIntervals.of_fin 1034200 200 complete_chunk5171

lemma complete_chunk5172 : ∀ i : Fin 200, Compatible (1034400 + i.val) →
    (table.lookup (1034400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5172 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1034400 1034600 :=
  FiniteIntervals.of_fin 1034400 200 complete_chunk5172

lemma complete_chunk5173 : ∀ i : Fin 200, Compatible (1034600 + i.val) →
    (table.lookup (1034600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5173 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1034600 1034800 :=
  FiniteIntervals.of_fin 1034600 200 complete_chunk5173

lemma complete_chunk5174 : ∀ i : Fin 200, Compatible (1034800 + i.val) →
    (table.lookup (1034800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5174 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1034800 1035000 :=
  FiniteIntervals.of_fin 1034800 200 complete_chunk5174

lemma complete_chunk5175 : ∀ i : Fin 200, Compatible (1035000 + i.val) →
    (table.lookup (1035000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5175 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1035000 1035200 :=
  FiniteIntervals.of_fin 1035000 200 complete_chunk5175

lemma complete_chunk5176 : ∀ i : Fin 200, Compatible (1035200 + i.val) →
    (table.lookup (1035200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5176 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1035200 1035400 :=
  FiniteIntervals.of_fin 1035200 200 complete_chunk5176

lemma complete_chunk5177 : ∀ i : Fin 200, Compatible (1035400 + i.val) →
    (table.lookup (1035400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5177 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1035400 1035600 :=
  FiniteIntervals.of_fin 1035400 200 complete_chunk5177

lemma complete_chunk5178 : ∀ i : Fin 200, Compatible (1035600 + i.val) →
    (table.lookup (1035600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5178 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1035600 1035800 :=
  FiniteIntervals.of_fin 1035600 200 complete_chunk5178

lemma complete_chunk5179 : ∀ i : Fin 200, Compatible (1035800 + i.val) →
    (table.lookup (1035800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5179 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1035800 1036000 :=
  FiniteIntervals.of_fin 1035800 200 complete_chunk5179

#print axioms interval_chunk5170
end Erdos184Work.PureFiveFilter4
