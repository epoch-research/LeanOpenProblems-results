import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4970 : ∀ i : Fin 200, Compatible (994000 + i.val) →
    (table.lookup (994000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4970 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 994000 994200 :=
  FiniteIntervals.of_fin 994000 200 complete_chunk4970

lemma complete_chunk4971 : ∀ i : Fin 200, Compatible (994200 + i.val) →
    (table.lookup (994200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4971 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 994200 994400 :=
  FiniteIntervals.of_fin 994200 200 complete_chunk4971

lemma complete_chunk4972 : ∀ i : Fin 200, Compatible (994400 + i.val) →
    (table.lookup (994400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4972 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 994400 994600 :=
  FiniteIntervals.of_fin 994400 200 complete_chunk4972

lemma complete_chunk4973 : ∀ i : Fin 200, Compatible (994600 + i.val) →
    (table.lookup (994600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4973 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 994600 994800 :=
  FiniteIntervals.of_fin 994600 200 complete_chunk4973

lemma complete_chunk4974 : ∀ i : Fin 200, Compatible (994800 + i.val) →
    (table.lookup (994800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4974 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 994800 995000 :=
  FiniteIntervals.of_fin 994800 200 complete_chunk4974

lemma complete_chunk4975 : ∀ i : Fin 200, Compatible (995000 + i.val) →
    (table.lookup (995000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4975 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 995000 995200 :=
  FiniteIntervals.of_fin 995000 200 complete_chunk4975

lemma complete_chunk4976 : ∀ i : Fin 200, Compatible (995200 + i.val) →
    (table.lookup (995200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4976 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 995200 995400 :=
  FiniteIntervals.of_fin 995200 200 complete_chunk4976

lemma complete_chunk4977 : ∀ i : Fin 200, Compatible (995400 + i.val) →
    (table.lookup (995400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4977 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 995400 995600 :=
  FiniteIntervals.of_fin 995400 200 complete_chunk4977

lemma complete_chunk4978 : ∀ i : Fin 200, Compatible (995600 + i.val) →
    (table.lookup (995600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4978 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 995600 995800 :=
  FiniteIntervals.of_fin 995600 200 complete_chunk4978

lemma complete_chunk4979 : ∀ i : Fin 200, Compatible (995800 + i.val) →
    (table.lookup (995800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4979 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 995800 996000 :=
  FiniteIntervals.of_fin 995800 200 complete_chunk4979

#print axioms interval_chunk4970
end Erdos184Work.PureFiveFilter4
