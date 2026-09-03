import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4660 : ∀ i : Fin 200, Compatible (932000 + i.val) →
    (table.lookup (932000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4660 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 932000 932200 :=
  FiniteIntervals.of_fin 932000 200 complete_chunk4660

lemma complete_chunk4661 : ∀ i : Fin 200, Compatible (932200 + i.val) →
    (table.lookup (932200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4661 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 932200 932400 :=
  FiniteIntervals.of_fin 932200 200 complete_chunk4661

lemma complete_chunk4662 : ∀ i : Fin 200, Compatible (932400 + i.val) →
    (table.lookup (932400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4662 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 932400 932600 :=
  FiniteIntervals.of_fin 932400 200 complete_chunk4662

lemma complete_chunk4663 : ∀ i : Fin 200, Compatible (932600 + i.val) →
    (table.lookup (932600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4663 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 932600 932800 :=
  FiniteIntervals.of_fin 932600 200 complete_chunk4663

lemma complete_chunk4664 : ∀ i : Fin 200, Compatible (932800 + i.val) →
    (table.lookup (932800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4664 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 932800 933000 :=
  FiniteIntervals.of_fin 932800 200 complete_chunk4664

lemma complete_chunk4665 : ∀ i : Fin 200, Compatible (933000 + i.val) →
    (table.lookup (933000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4665 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 933000 933200 :=
  FiniteIntervals.of_fin 933000 200 complete_chunk4665

lemma complete_chunk4666 : ∀ i : Fin 200, Compatible (933200 + i.val) →
    (table.lookup (933200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4666 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 933200 933400 :=
  FiniteIntervals.of_fin 933200 200 complete_chunk4666

lemma complete_chunk4667 : ∀ i : Fin 200, Compatible (933400 + i.val) →
    (table.lookup (933400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4667 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 933400 933600 :=
  FiniteIntervals.of_fin 933400 200 complete_chunk4667

lemma complete_chunk4668 : ∀ i : Fin 200, Compatible (933600 + i.val) →
    (table.lookup (933600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4668 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 933600 933800 :=
  FiniteIntervals.of_fin 933600 200 complete_chunk4668

lemma complete_chunk4669 : ∀ i : Fin 200, Compatible (933800 + i.val) →
    (table.lookup (933800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4669 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 933800 934000 :=
  FiniteIntervals.of_fin 933800 200 complete_chunk4669

#print axioms interval_chunk4660
end Erdos184Work.PureFiveFilter4
