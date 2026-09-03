import Submission.PureFiveFilter4
import Submission.FiniteIntervals

/-! Kernel checks for a consecutive block of raw five-color keys. -/
namespace Erdos184Work.PureFiveFilter4
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option Elab.async false

lemma complete_chunk690 : ∀ i : Fin 200, Compatible (138000 + i.val) →
    (table.lookup (138000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk690 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 138000 138200 :=
  FiniteIntervals.of_fin 138000 200 complete_chunk690

lemma complete_chunk691 : ∀ i : Fin 200, Compatible (138200 + i.val) →
    (table.lookup (138200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk691 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 138200 138400 :=
  FiniteIntervals.of_fin 138200 200 complete_chunk691

lemma complete_chunk692 : ∀ i : Fin 200, Compatible (138400 + i.val) →
    (table.lookup (138400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk692 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 138400 138600 :=
  FiniteIntervals.of_fin 138400 200 complete_chunk692

lemma complete_chunk693 : ∀ i : Fin 200, Compatible (138600 + i.val) →
    (table.lookup (138600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk693 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 138600 138800 :=
  FiniteIntervals.of_fin 138600 200 complete_chunk693

lemma complete_chunk694 : ∀ i : Fin 200, Compatible (138800 + i.val) →
    (table.lookup (138800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk694 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 138800 139000 :=
  FiniteIntervals.of_fin 138800 200 complete_chunk694

lemma complete_chunk695 : ∀ i : Fin 200, Compatible (139000 + i.val) →
    (table.lookup (139000 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk695 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 139000 139200 :=
  FiniteIntervals.of_fin 139000 200 complete_chunk695

lemma complete_chunk696 : ∀ i : Fin 200, Compatible (139200 + i.val) →
    (table.lookup (139200 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk696 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 139200 139400 :=
  FiniteIntervals.of_fin 139200 200 complete_chunk696

lemma complete_chunk697 : ∀ i : Fin 200, Compatible (139400 + i.val) →
    (table.lookup (139400 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk697 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 139400 139600 :=
  FiniteIntervals.of_fin 139400 200 complete_chunk697

lemma complete_chunk698 : ∀ i : Fin 200, Compatible (139600 + i.val) →
    (table.lookup (139600 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk698 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 139600 139800 :=
  FiniteIntervals.of_fin 139600 200 complete_chunk698

lemma complete_chunk699 : ∀ i : Fin 200, Compatible (139800 + i.val) →
    (table.lookup (139800 + i.val)).isSome = true := by decide +kernel
lemma interval_chunk699 : FiniteIntervals.Covers (fun j => Compatible j → (table.lookup j).isSome = true) 139800 140000 :=
  FiniteIntervals.of_fin 139800 200 complete_chunk699

#print axioms interval_chunk690
end Erdos184Work.PureFiveFilter4
