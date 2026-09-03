import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk680 : ∀ i : Fin 200, Compatible (136000 + i.val) →
    (table.lookup (136000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk680 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 136000 136200 :=
  FiniteIntervals.of_fin 136000 200 complete_chunk680

lemma complete_chunk681 : ∀ i : Fin 200, Compatible (136200 + i.val) →
    (table.lookup (136200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk681 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 136200 136400 :=
  FiniteIntervals.of_fin 136200 200 complete_chunk681

lemma complete_chunk682 : ∀ i : Fin 200, Compatible (136400 + i.val) →
    (table.lookup (136400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk682 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 136400 136600 :=
  FiniteIntervals.of_fin 136400 200 complete_chunk682

lemma complete_chunk683 : ∀ i : Fin 200, Compatible (136600 + i.val) →
    (table.lookup (136600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk683 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 136600 136800 :=
  FiniteIntervals.of_fin 136600 200 complete_chunk683

lemma complete_chunk684 : ∀ i : Fin 200, Compatible (136800 + i.val) →
    (table.lookup (136800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk684 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 136800 137000 :=
  FiniteIntervals.of_fin 136800 200 complete_chunk684

lemma complete_chunk685 : ∀ i : Fin 200, Compatible (137000 + i.val) →
    (table.lookup (137000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk685 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 137000 137200 :=
  FiniteIntervals.of_fin 137000 200 complete_chunk685

lemma complete_chunk686 : ∀ i : Fin 200, Compatible (137200 + i.val) →
    (table.lookup (137200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk686 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 137200 137400 :=
  FiniteIntervals.of_fin 137200 200 complete_chunk686

lemma complete_chunk687 : ∀ i : Fin 200, Compatible (137400 + i.val) →
    (table.lookup (137400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk687 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 137400 137600 :=
  FiniteIntervals.of_fin 137400 200 complete_chunk687

lemma complete_chunk688 : ∀ i : Fin 200, Compatible (137600 + i.val) →
    (table.lookup (137600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk688 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 137600 137800 :=
  FiniteIntervals.of_fin 137600 200 complete_chunk688

lemma complete_chunk689 : ∀ i : Fin 200, Compatible (137800 + i.val) →
    (table.lookup (137800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk689 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 137800 138000 :=
  FiniteIntervals.of_fin 137800 200 complete_chunk689

#print axioms interval_chunk680
end Erdos184Work.PureFiveFilter4
