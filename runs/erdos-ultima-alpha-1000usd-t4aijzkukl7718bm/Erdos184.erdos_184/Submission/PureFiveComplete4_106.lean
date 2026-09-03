import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk1060 : ∀ i : Fin 200, Compatible (212000 + i.val) →
    (table.lookup (212000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1060 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 212000 212200 :=
  FiniteIntervals.of_fin 212000 200 complete_chunk1060

lemma complete_chunk1061 : ∀ i : Fin 200, Compatible (212200 + i.val) →
    (table.lookup (212200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1061 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 212200 212400 :=
  FiniteIntervals.of_fin 212200 200 complete_chunk1061

lemma complete_chunk1062 : ∀ i : Fin 200, Compatible (212400 + i.val) →
    (table.lookup (212400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1062 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 212400 212600 :=
  FiniteIntervals.of_fin 212400 200 complete_chunk1062

lemma complete_chunk1063 : ∀ i : Fin 200, Compatible (212600 + i.val) →
    (table.lookup (212600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1063 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 212600 212800 :=
  FiniteIntervals.of_fin 212600 200 complete_chunk1063

lemma complete_chunk1064 : ∀ i : Fin 200, Compatible (212800 + i.val) →
    (table.lookup (212800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1064 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 212800 213000 :=
  FiniteIntervals.of_fin 212800 200 complete_chunk1064

lemma complete_chunk1065 : ∀ i : Fin 200, Compatible (213000 + i.val) →
    (table.lookup (213000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1065 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 213000 213200 :=
  FiniteIntervals.of_fin 213000 200 complete_chunk1065

lemma complete_chunk1066 : ∀ i : Fin 200, Compatible (213200 + i.val) →
    (table.lookup (213200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1066 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 213200 213400 :=
  FiniteIntervals.of_fin 213200 200 complete_chunk1066

lemma complete_chunk1067 : ∀ i : Fin 200, Compatible (213400 + i.val) →
    (table.lookup (213400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1067 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 213400 213600 :=
  FiniteIntervals.of_fin 213400 200 complete_chunk1067

lemma complete_chunk1068 : ∀ i : Fin 200, Compatible (213600 + i.val) →
    (table.lookup (213600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1068 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 213600 213800 :=
  FiniteIntervals.of_fin 213600 200 complete_chunk1068

lemma complete_chunk1069 : ∀ i : Fin 200, Compatible (213800 + i.val) →
    (table.lookup (213800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk1069 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 213800 214000 :=
  FiniteIntervals.of_fin 213800 200 complete_chunk1069

#print axioms interval_chunk1060
end Erdos184Work.PureFiveFilter4
