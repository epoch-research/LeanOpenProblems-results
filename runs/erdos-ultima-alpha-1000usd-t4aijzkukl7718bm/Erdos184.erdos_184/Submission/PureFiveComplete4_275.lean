import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk2750 : ∀ i : Fin 200, Compatible (550000 + i.val) →
    (table.lookup (550000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2750 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 550000 550200 :=
  FiniteIntervals.of_fin 550000 200 complete_chunk2750

lemma complete_chunk2751 : ∀ i : Fin 200, Compatible (550200 + i.val) →
    (table.lookup (550200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2751 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 550200 550400 :=
  FiniteIntervals.of_fin 550200 200 complete_chunk2751

lemma complete_chunk2752 : ∀ i : Fin 200, Compatible (550400 + i.val) →
    (table.lookup (550400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2752 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 550400 550600 :=
  FiniteIntervals.of_fin 550400 200 complete_chunk2752

lemma complete_chunk2753 : ∀ i : Fin 200, Compatible (550600 + i.val) →
    (table.lookup (550600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2753 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 550600 550800 :=
  FiniteIntervals.of_fin 550600 200 complete_chunk2753

lemma complete_chunk2754 : ∀ i : Fin 200, Compatible (550800 + i.val) →
    (table.lookup (550800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2754 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 550800 551000 :=
  FiniteIntervals.of_fin 550800 200 complete_chunk2754

lemma complete_chunk2755 : ∀ i : Fin 200, Compatible (551000 + i.val) →
    (table.lookup (551000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2755 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 551000 551200 :=
  FiniteIntervals.of_fin 551000 200 complete_chunk2755

lemma complete_chunk2756 : ∀ i : Fin 200, Compatible (551200 + i.val) →
    (table.lookup (551200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2756 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 551200 551400 :=
  FiniteIntervals.of_fin 551200 200 complete_chunk2756

lemma complete_chunk2757 : ∀ i : Fin 200, Compatible (551400 + i.val) →
    (table.lookup (551400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2757 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 551400 551600 :=
  FiniteIntervals.of_fin 551400 200 complete_chunk2757

lemma complete_chunk2758 : ∀ i : Fin 200, Compatible (551600 + i.val) →
    (table.lookup (551600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2758 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 551600 551800 :=
  FiniteIntervals.of_fin 551600 200 complete_chunk2758

lemma complete_chunk2759 : ∀ i : Fin 200, Compatible (551800 + i.val) →
    (table.lookup (551800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk2759 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 551800 552000 :=
  FiniteIntervals.of_fin 551800 200 complete_chunk2759

#print axioms interval_chunk2750
end Erdos184Work.PureFiveFilter4
