import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5710 : ∀ i : Fin 200, Compatible (1142000 + i.val) →
    (table.lookup (1142000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5710 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1142000 1142200 :=
  FiniteIntervals.of_fin 1142000 200 complete_chunk5710

lemma complete_chunk5711 : ∀ i : Fin 200, Compatible (1142200 + i.val) →
    (table.lookup (1142200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5711 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1142200 1142400 :=
  FiniteIntervals.of_fin 1142200 200 complete_chunk5711

lemma complete_chunk5712 : ∀ i : Fin 200, Compatible (1142400 + i.val) →
    (table.lookup (1142400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5712 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1142400 1142600 :=
  FiniteIntervals.of_fin 1142400 200 complete_chunk5712

lemma complete_chunk5713 : ∀ i : Fin 200, Compatible (1142600 + i.val) →
    (table.lookup (1142600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5713 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1142600 1142800 :=
  FiniteIntervals.of_fin 1142600 200 complete_chunk5713

lemma complete_chunk5714 : ∀ i : Fin 200, Compatible (1142800 + i.val) →
    (table.lookup (1142800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5714 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1142800 1143000 :=
  FiniteIntervals.of_fin 1142800 200 complete_chunk5714

lemma complete_chunk5715 : ∀ i : Fin 200, Compatible (1143000 + i.val) →
    (table.lookup (1143000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5715 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1143000 1143200 :=
  FiniteIntervals.of_fin 1143000 200 complete_chunk5715

lemma complete_chunk5716 : ∀ i : Fin 200, Compatible (1143200 + i.val) →
    (table.lookup (1143200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5716 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1143200 1143400 :=
  FiniteIntervals.of_fin 1143200 200 complete_chunk5716

lemma complete_chunk5717 : ∀ i : Fin 200, Compatible (1143400 + i.val) →
    (table.lookup (1143400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5717 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1143400 1143600 :=
  FiniteIntervals.of_fin 1143400 200 complete_chunk5717

lemma complete_chunk5718 : ∀ i : Fin 200, Compatible (1143600 + i.val) →
    (table.lookup (1143600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5718 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1143600 1143800 :=
  FiniteIntervals.of_fin 1143600 200 complete_chunk5718

lemma complete_chunk5719 : ∀ i : Fin 200, Compatible (1143800 + i.val) →
    (table.lookup (1143800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5719 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1143800 1144000 :=
  FiniteIntervals.of_fin 1143800 200 complete_chunk5719

#print axioms interval_chunk5710
end Erdos184Work.PureFiveFilter4
