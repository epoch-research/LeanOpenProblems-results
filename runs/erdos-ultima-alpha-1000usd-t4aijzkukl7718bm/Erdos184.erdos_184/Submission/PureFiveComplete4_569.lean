import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk5690 : ∀ i : Fin 200, Compatible (1138000 + i.val) →
    (table.lookup (1138000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5690 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1138000 1138200 :=
  FiniteIntervals.of_fin 1138000 200 complete_chunk5690

lemma complete_chunk5691 : ∀ i : Fin 200, Compatible (1138200 + i.val) →
    (table.lookup (1138200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5691 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1138200 1138400 :=
  FiniteIntervals.of_fin 1138200 200 complete_chunk5691

lemma complete_chunk5692 : ∀ i : Fin 200, Compatible (1138400 + i.val) →
    (table.lookup (1138400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5692 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1138400 1138600 :=
  FiniteIntervals.of_fin 1138400 200 complete_chunk5692

lemma complete_chunk5693 : ∀ i : Fin 200, Compatible (1138600 + i.val) →
    (table.lookup (1138600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5693 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1138600 1138800 :=
  FiniteIntervals.of_fin 1138600 200 complete_chunk5693

lemma complete_chunk5694 : ∀ i : Fin 200, Compatible (1138800 + i.val) →
    (table.lookup (1138800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5694 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1138800 1139000 :=
  FiniteIntervals.of_fin 1138800 200 complete_chunk5694

lemma complete_chunk5695 : ∀ i : Fin 200, Compatible (1139000 + i.val) →
    (table.lookup (1139000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5695 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1139000 1139200 :=
  FiniteIntervals.of_fin 1139000 200 complete_chunk5695

lemma complete_chunk5696 : ∀ i : Fin 200, Compatible (1139200 + i.val) →
    (table.lookup (1139200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5696 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1139200 1139400 :=
  FiniteIntervals.of_fin 1139200 200 complete_chunk5696

lemma complete_chunk5697 : ∀ i : Fin 200, Compatible (1139400 + i.val) →
    (table.lookup (1139400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5697 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1139400 1139600 :=
  FiniteIntervals.of_fin 1139400 200 complete_chunk5697

lemma complete_chunk5698 : ∀ i : Fin 200, Compatible (1139600 + i.val) →
    (table.lookup (1139600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5698 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1139600 1139800 :=
  FiniteIntervals.of_fin 1139600 200 complete_chunk5698

lemma complete_chunk5699 : ∀ i : Fin 200, Compatible (1139800 + i.val) →
    (table.lookup (1139800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk5699 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 1139800 1140000 :=
  FiniteIntervals.of_fin 1139800 200 complete_chunk5699

#print axioms interval_chunk5690
end Erdos184Work.PureFiveFilter4
