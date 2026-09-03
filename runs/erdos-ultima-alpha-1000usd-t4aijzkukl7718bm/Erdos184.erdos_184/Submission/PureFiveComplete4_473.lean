import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk4730 : ∀ i : Fin 200, Compatible (946000 + i.val) →
    (table.lookup (946000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4730 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 946000 946200 :=
  FiniteIntervals.of_fin 946000 200 complete_chunk4730

lemma complete_chunk4731 : ∀ i : Fin 200, Compatible (946200 + i.val) →
    (table.lookup (946200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4731 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 946200 946400 :=
  FiniteIntervals.of_fin 946200 200 complete_chunk4731

lemma complete_chunk4732 : ∀ i : Fin 200, Compatible (946400 + i.val) →
    (table.lookup (946400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4732 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 946400 946600 :=
  FiniteIntervals.of_fin 946400 200 complete_chunk4732

lemma complete_chunk4733 : ∀ i : Fin 200, Compatible (946600 + i.val) →
    (table.lookup (946600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4733 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 946600 946800 :=
  FiniteIntervals.of_fin 946600 200 complete_chunk4733

lemma complete_chunk4734 : ∀ i : Fin 200, Compatible (946800 + i.val) →
    (table.lookup (946800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4734 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 946800 947000 :=
  FiniteIntervals.of_fin 946800 200 complete_chunk4734

lemma complete_chunk4735 : ∀ i : Fin 200, Compatible (947000 + i.val) →
    (table.lookup (947000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4735 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 947000 947200 :=
  FiniteIntervals.of_fin 947000 200 complete_chunk4735

lemma complete_chunk4736 : ∀ i : Fin 200, Compatible (947200 + i.val) →
    (table.lookup (947200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4736 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 947200 947400 :=
  FiniteIntervals.of_fin 947200 200 complete_chunk4736

lemma complete_chunk4737 : ∀ i : Fin 200, Compatible (947400 + i.val) →
    (table.lookup (947400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4737 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 947400 947600 :=
  FiniteIntervals.of_fin 947400 200 complete_chunk4737

lemma complete_chunk4738 : ∀ i : Fin 200, Compatible (947600 + i.val) →
    (table.lookup (947600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4738 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 947600 947800 :=
  FiniteIntervals.of_fin 947600 200 complete_chunk4738

lemma complete_chunk4739 : ∀ i : Fin 200, Compatible (947800 + i.val) →
    (table.lookup (947800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk4739 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 947800 948000 :=
  FiniteIntervals.of_fin 947800 200 complete_chunk4739

#print axioms interval_chunk4730
end Erdos184Work.PureFiveFilter4
