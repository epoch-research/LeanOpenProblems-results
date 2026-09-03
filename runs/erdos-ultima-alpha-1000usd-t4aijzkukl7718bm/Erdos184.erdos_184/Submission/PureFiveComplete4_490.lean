import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4900 : ∀ i : Fin 200, Compatible (980000 + i.val) →
    (table.lookup (980000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4900 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 980000 980200 :=
  FiniteIntervals.of_fin 980000 200 complete_chunk4900

lemma complete_chunk4901 : ∀ i : Fin 200, Compatible (980200 + i.val) →
    (table.lookup (980200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4901 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 980200 980400 :=
  FiniteIntervals.of_fin 980200 200 complete_chunk4901

lemma complete_chunk4902 : ∀ i : Fin 200, Compatible (980400 + i.val) →
    (table.lookup (980400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4902 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 980400 980600 :=
  FiniteIntervals.of_fin 980400 200 complete_chunk4902

lemma complete_chunk4903 : ∀ i : Fin 200, Compatible (980600 + i.val) →
    (table.lookup (980600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4903 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 980600 980800 :=
  FiniteIntervals.of_fin 980600 200 complete_chunk4903

lemma complete_chunk4904 : ∀ i : Fin 200, Compatible (980800 + i.val) →
    (table.lookup (980800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4904 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 980800 981000 :=
  FiniteIntervals.of_fin 980800 200 complete_chunk4904

lemma complete_chunk4905 : ∀ i : Fin 200, Compatible (981000 + i.val) →
    (table.lookup (981000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4905 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 981000 981200 :=
  FiniteIntervals.of_fin 981000 200 complete_chunk4905

lemma complete_chunk4906 : ∀ i : Fin 200, Compatible (981200 + i.val) →
    (table.lookup (981200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4906 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 981200 981400 :=
  FiniteIntervals.of_fin 981200 200 complete_chunk4906

lemma complete_chunk4907 : ∀ i : Fin 200, Compatible (981400 + i.val) →
    (table.lookup (981400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4907 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 981400 981600 :=
  FiniteIntervals.of_fin 981400 200 complete_chunk4907

lemma complete_chunk4908 : ∀ i : Fin 200, Compatible (981600 + i.val) →
    (table.lookup (981600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4908 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 981600 981800 :=
  FiniteIntervals.of_fin 981600 200 complete_chunk4908

lemma complete_chunk4909 : ∀ i : Fin 200, Compatible (981800 + i.val) →
    (table.lookup (981800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4909 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 981800 982000 :=
  FiniteIntervals.of_fin 981800 200 complete_chunk4909

#print axioms interval_chunk4900
end Erdos184Work.PureFiveFilter4
